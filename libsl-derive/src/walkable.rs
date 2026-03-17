use proc_macro2::TokenStream;
use quote::{quote, quote_spanned};
use syn::spanned::Spanned;
use syn::{AttrStyle, Data, Field, Fields, Ident};

use crate::field_binding_ident;

pub fn generate_walkable(name: &Ident, data: &Data) -> TokenStream {
    match data {
        Data::Struct(data) => {
            let field_pat = make_field_pattern(&data.fields);
            let walk = walk_fields(&data.fields);

            quote! {
                let #name #field_pat = self;
                #walk
            }
        }

        Data::Enum(data) => {
            let variants = data.variants.iter().map(|variant| {
                let variant_name = &variant.ident;
                let field_pat = make_field_pattern(&variant.fields);
                let walk = walk_fields(&variant.fields);

                quote! {
                    #name::#variant_name #field_pat => {
                        #walk
                    }
                }
            });

            quote! {
                match self {
                    #(#variants)*
                }
            }
        }

        Data::Union(_) => unimplemented!(),
    }
}

fn no_walk(field: &Field) -> bool {
    field.attrs.iter().any(|attr| {
        matches!(attr.style, AttrStyle::Outer)
            && matches!(&attr.meta, syn::Meta::Path(path) if path.is_ident("no_walk"))
    })
}

fn make_field_pattern(fields: &Fields) -> TokenStream {
    match fields {
        Fields::Named(fields) => {
            let names = fields
                .named
                .iter()
                .map(|field| field.ident.clone().unwrap());

            quote! {
                { #(#names),* }
            }
        }

        Fields::Unnamed(fields) => {
            let names = (0..fields.unnamed.len()).map(field_binding_ident);

            quote! {
                (#(#names),*)
            }
        }

        Fields::Unit => Default::default(),
    }
}

fn walk_field(ident: &Ident, field: &Field) -> TokenStream {
    let span = match &field.ident {
        Some(ident) => ident.span(),
        None => field.ty.span(),
    };
    let ty = &field.ty;

    if no_walk(field) {
        quote_spanned! {span=>
            let _ = #ident;
            ::static_assertions::assert_not_impl_any!(#ty: crate::visit::Walkable);
        }
    } else {
        quote_spanned! {span=>
            crate::visit::Walkable::walk(#ident, visitor, ctx.clone())?;
        }
    }
}

fn walk_fields(fields: &Fields) -> TokenStream {
    match fields {
        Fields::Named(fields) => fields
            .named
            .iter()
            .map(|field| walk_field(field.ident.as_ref().unwrap(), field))
            .collect(),

        Fields::Unnamed(fields) => fields
            .unnamed
            .iter()
            .enumerate()
            .map(|(idx, field)| {
                let ident = field_binding_ident(idx);

                walk_field(&ident, field)
            })
            .collect(),

        Fields::Unit => Default::default(),
    }
}
