extern crate proc_macro;

use proc_macro::TokenStream;
use quote::*;
use syn::*;

#[proc_macro_derive(Pod)]
pub fn derive_pod(item: TokenStream) -> TokenStream {
    let item = parse_macro_input!(item as DeriveInput);

    let ident = item.ident;
    let fields = match &item.data {
        Data::Union(data) => data.fields.named.iter().map(|field| &field.ty).collect(),
        Data::Struct(data) => match &data.fields {
            Fields::Named(fields) => fields.named.iter().map(|field| &field.ty).collect(),
            Fields::Unnamed(fields) => fields.unnamed.iter().map(|field| &field.ty).collect(),
            Fields::Unit => vec![]
        },
        Data::Enum(_) => panic!("Enums are not supported"),
    };

    quote!(
        const _: () = {
            extern crate pod2;
            use std::mem;
            
            unsafe impl pod2::Pod for #ident {}

            const _: fn() = || {
                #[allow(unused)]
                fn assert_pod<T: pod2::Pod>() {}
                #( assert_pod::<#fields>(); )*
            };
        };
    ).into()
}