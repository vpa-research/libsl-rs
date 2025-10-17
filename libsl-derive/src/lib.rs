use quote::{format_ident, quote};
use syn::{DeriveInput, Ident, parse_macro_input};

use crate::serialize::generate_serialize;
use crate::walkable::generate_walkable;

mod serialize;
mod walkable;

fn field_binding_ident(idx: usize) -> Ident {
    format_ident!("__field{idx}")
}

#[proc_macro_derive(Serialize, attributes(no_wrap))]
pub fn derive_serialize(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
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

#[proc_macro_derive(Walkable, attributes(no_walk))]
pub fn derive_walkable(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input: DeriveInput = parse_macro_input!(input as DeriveInput);
    let name = input.ident;

    if !input.generics.params.is_empty() || input.generics.where_clause.is_some() {
        panic!("generic items are not supported by this derive macro");
    }

    let walkable_body = generate_walkable(&name, &input.data);

    proc_macro::TokenStream::from(quote! {
        impl crate::visit::Walkable for #name {
            fn walk<'ast, V>(&'ast self, visitor: &mut V) -> ::std::ops::ControlFlow<()>
            where
                V: crate::visit::Visitor<'ast> + ?Sized,
            {
                #walkable_body

                ::std::ops::ControlFlow::Continue(())
            }
        }
    })
}
