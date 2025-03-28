use proc_macro2::TokenStream;
use quote::{ToTokens, format_ident, quote, quote_spanned};
use syn::spanned::Spanned;
use syn::{
    AttrStyle, Data, DeriveInput, Field, Fields, FieldsNamed, FieldsUnnamed, Ident, Index, LitStr,
    parse_macro_input,
};

#[proc_macro_derive(Serialize, attributes(no_wrap))]
pub fn derive_serialize_for_nodes(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input: DeriveInput = parse_macro_input!(input as DeriveInput);
    let name = input.ident;

    if !input.generics.params.is_empty() || input.generics.where_clause.is_some() {
        panic!("generic items are not supported by this derive macro");
    }

    let serialize_body = generate_serialize(&name, &input.data);

    proc_macro::TokenStream::from(quote! {
        #[cfg(feature = "serde")]
        impl ::serde::Serialize for crate::LibSlNode<'_, #name> {
            fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
            where
                S: ::serde::Serializer,
            {
                #serialize_body
            }
        }
    })
}

fn field_binding_ident(idx: usize) -> Ident {
    format_ident!("__field{idx}")
}

fn generate_serialize(name: &Ident, data: &Data) -> TokenStream {
    let name_str = name.to_string();
    let name_lit = LitStr::new(&name_str, name.span());

    match data {
        Data::Struct(data) => match &data.fields {
            Fields::Named(fields) => generate_serialize_for_struct(&name_lit, fields),
            Fields::Unnamed(fields) if fields.unnamed.len() == 1 => {
                generate_serialize_for_newtype_struct(&name_lit, fields)
            }
            Fields::Unnamed(fields) => generate_serialize_for_tuple_struct(&name_lit, fields),
            Fields::Unit => generate_serialize_for_unit_struct(&name_lit),
        },

        Data::Enum(data) => {
            let ser_variants = data.variants.iter().enumerate().map(|(idx, variant)| {
                let idx = idx as u32;
                let variant_name = &variant.ident;
                let variant_name_str = variant_name.to_string();
                let variant_name_lit = LitStr::new(&variant_name_str, variant_name.span());

                let ser_variant = match &variant.fields {
                    Fields::Named(fields) => generate_serialize_for_struct_variant(
                        &name_lit,
                        idx,
                        &variant_name_lit,
                        fields,
                    ),

                    Fields::Unnamed(fields) if fields.unnamed.len() == 1 => {
                        generate_serialize_for_newtype_variant(
                            &name_lit,
                            idx,
                            &variant_name_lit,
                            fields,
                        )
                    }

                    Fields::Unnamed(fields) => generate_serialize_for_tuple_variant(
                        &name_lit,
                        idx,
                        &variant_name_lit,
                        fields,
                    ),

                    Fields::Unit => {
                        generate_serialize_for_unit_variant(&name_lit, idx, &variant_name_lit)
                    }
                };

                let variant_fields = match &variant.fields {
                    Fields::Named(fields) => {
                        let field_names = fields.named.iter().enumerate().map(|(idx, field)| {
                            let field_name = &field.ident;
                            let binding_name = field_binding_ident(idx);

                            quote! {
                                #field_name: #binding_name
                            }
                        });

                        quote! {
                            { #(#field_names),* }
                        }
                    }

                    Fields::Unnamed(fields) => {
                        let field_names = (0..fields.unnamed.len()).map(|idx| {
                            let binding_name = field_binding_ident(idx);

                            quote! { #binding_name }
                        });

                        quote! {
                            (#(#field_names),*)
                        }
                    }

                    Fields::Unit => quote!(),
                };

                quote! {
                    #name::#variant_name #variant_fields => {
                        #ser_variant
                    }
                }
            });

            quote! {
                match self.inner() {
                    #(#ser_variants)*
                }
            }
        }

        Data::Union(_) => unimplemented!(),
    }
}

fn generate_serialize_for_struct_fields(
    fields: &FieldsNamed,
    serializer: &TokenStream,
    is_enum: bool,
) -> impl Iterator<Item = TokenStream> {
    fields.named.iter().enumerate().map(move |(idx, field)| {
        let field_name = field.ident.as_ref().unwrap();
        let field_name_str = field_name.to_string();
        let field_name_lit = LitStr::new(&field_name_str, field_name.span());
        let field_expr = generate_field_expr(idx, field, is_enum);
        let trait_name = if is_enum {
            quote! { SerializeStructVariant }
        } else {
            quote! { SerializeStruct }
        };

        quote_spanned! {field.span()=>
            <S::#trait_name as ::serde::ser::#trait_name>::serialize_field(
                &mut #serializer,
                #field_name_lit,
                #field_expr,
            )?;
        }
    })
}

fn generate_serialize_for_struct(name_lit: &LitStr, fields: &FieldsNamed) -> TokenStream {
    let field_count = fields.named.len();
    let serializer = quote! { s };
    let ser_fields = generate_serialize_for_struct_fields(fields, &serializer, false);

    quote! {
        let mut #serializer = serializer.serialize_struct(#name_lit, #field_count)?;
        #(#ser_fields)*

        <S::SerializeStruct as ::serde::ser::SerializeStruct>::end(#serializer)
    }
}

fn generate_serialize_for_struct_variant(
    name_lit: &LitStr,
    variant_idx: u32,
    variant_name_lit: &LitStr,
    fields: &FieldsNamed,
) -> TokenStream {
    let field_count = fields.named.len();
    let serializer = quote! { sv };
    let ser_fields = generate_serialize_for_struct_fields(fields, &serializer, true);

    quote! {
        let mut #serializer = serializer.serializer_struct_variant(
            #name_lit,
            #variant_idx,
            #variant_name_lit,
            #field_count,
        )?;
        #(#ser_fields)*

        <S::SerializeStructVariant as ::serde::ser::SerializeStructVariant>::end(#serializer)
    }
}

fn generate_serialize_for_newtype_struct(name_lit: &LitStr, fields: &FieldsUnnamed) -> TokenStream {
    let field_expr = generate_field_expr(0, &fields.unnamed[0], false);

    quote! {
        serializer.serialize_newtype_struct(#name_lit, #field_expr)
    }
}

fn generate_serialize_for_newtype_variant(
    name_lit: &LitStr,
    variant_idx: u32,
    variant_name_lit: &LitStr,
    fields: &FieldsUnnamed,
) -> TokenStream {
    let field_expr = generate_field_expr(0, &fields.unnamed[0], true);

    quote! {
        serializer.serialize_newtype_variant(
            #name_lit,
            #variant_idx,
            #variant_name_lit,
            #field_expr,
        )
    }
}

fn generate_serialize_for_tuple_struct_fields(
    fields: &FieldsUnnamed,
    serializer: &TokenStream,
    is_enum: bool,
) -> impl Iterator<Item = TokenStream> {
    fields.unnamed.iter().enumerate().map(move |(idx, field)| {
        let field_expr = generate_field_expr(idx, field, is_enum);
        let trait_name = if is_enum {
            quote! { SerializeTupleVariant }
        } else {
            quote! { SerializeTupleStruct }
        };

        quote_spanned! {field.span()=>
            <S::#trait_name as ::serde::ser::#trait_name>::serialize_field(
                &mut #serializer,
                #field_expr,
            )?;
        }
    })
}

fn generate_serialize_for_tuple_struct(name_lit: &LitStr, fields: &FieldsUnnamed) -> TokenStream {
    let field_count = fields.unnamed.len();
    let serializer = quote! { ts };
    let ser_fields = generate_serialize_for_tuple_struct_fields(fields, &serializer, false);

    quote! {
        let mut #serializer = serializer.serialize_tuple_struct(#name_lit, #field_count)?;
        #(#ser_fields)*

        <S::SerializeTupleStruct as ::serde::ser::SerializeTupleStruct>::end(#serializer)
    }
}

fn generate_serialize_for_tuple_variant(
    name_lit: &LitStr,
    variant_idx: u32,
    variant_name_lit: &LitStr,
    fields: &FieldsUnnamed,
) -> TokenStream {
    let field_count = fields.unnamed.len();
    let serializer = quote! { tv };
    let ser_fields = generate_serialize_for_tuple_struct_fields(fields, &serializer, true);

    quote! {
        let mut #serializer = serializer.serialize_tuple_variant(
            #name_lit,
            #variant_idx,
            #variant_name_lit,
            #field_count,
        )?;
        #(#ser_fields)*

        <S::SerializeTupleVariant as ::serde::ser::SerializeTupleVariant>::end(#serializer)
    }
}

fn generate_serialize_for_unit_struct(name_lit: &LitStr) -> TokenStream {
    quote! {
        serializer.serialize_unit_struct(#name_lit)
    }
}

fn generate_serialize_for_unit_variant(
    name_lit: &LitStr,
    variant_idx: u32,
    variant_name_lit: &LitStr,
) -> TokenStream {
    quote! {
        serializer.serialize_unit_variant(#name_lit, #variant_idx, #variant_name_lit)
    }
}

fn generate_field_expr(field_idx: usize, field: &Field, is_enum: bool) -> TokenStream {
    let name = match &field.ident {
        _ if is_enum => format_ident!("__field{field_idx}").into_token_stream(),
        Some(ident) => ident.to_token_stream(),
        None => Index::from(field_idx).into_token_stream(),
    };

    let no_wrap = field.attrs.iter().any(|attr| {
        matches!(attr.style, AttrStyle::Outer)
            && match &attr.meta {
                syn::Meta::Path(path) => path.is_ident("no_wrap"),
                _ => false,
            }
    });

    match (is_enum, no_wrap) {
        (true, true) => quote_spanned! {field.span()=>
            #name
        },

        (true, false) => quote_spanned! {field.span()=>
            &crate::LibSlNode::new(#name, self.libsl())
        },

        (false, true) => quote_spanned! {field.span()=>
            &self.inner().#name
        },

        (false, false) => quote_spanned! {field.span()=>
            &self.map(|inner| &inner.#name)
        },
    }
}
