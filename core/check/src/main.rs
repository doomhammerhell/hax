use quote::ToTokens;
use std::collections::HashMap;
use std::process::Command;
use syn::visit::Visit;

#[derive(Debug)]
struct Visitor {
    items: HashMap<Vec<String>, syn::Signature>,
    path: Vec<String>,
}

impl Visitor {
    pub fn new() -> Self {
        Self {
            items: HashMap::new(),
            path: Vec::new(),
        }
    }
}

impl<'ast> Visit<'ast> for Visitor {
    fn visit_item_mod(&mut self, i: &'ast syn::ItemMod) {
        self.path.push(i.ident.to_string());
        syn::visit::visit_item_mod(self, i);
        self.path.pop();
    }
    fn visit_item_fn(&mut self, i: &'ast syn::ItemFn) {
        self.path.push(i.sig.ident.to_string());
        self.items.insert(self.path.clone(), i.sig.clone());
        syn::visit::visit_item_fn(self, i);
        self.path.pop();
    }
}

fn parse_lib(path: &String) -> HashMap<Vec<String>, syn::Signature> {
    let mut cmd = Command::new("cargo");
    cmd.args(["expand", "--manifest-path", path]);
    let output = cmd.output().unwrap();
    let stdout = String::from_utf8(output.stdout).unwrap();
    let file: syn::File = syn::parse_str(&stdout).unwrap();
    let mut visitor = Visitor::new();
    visitor.visit_file(&file);
    visitor.items
}

fn main() {
    let lib_a = std::env::args().nth(1).unwrap();
    let lib_b = std::env::args().nth(2).unwrap();

    let items_a = parse_lib(&lib_a);
    let items_b = parse_lib(&lib_b);

    let res: Vec<_> = items_a
        .into_iter()
        .filter(|(path, sig)| items_b.get(path).map(|v| sig != v).unwrap_or(true))
        .map(|(_, sig)| sig.to_token_stream().to_string())
        .collect();

    if !res.is_empty() {
        for sig in res.iter() {
            eprintln!("{sig}");
        }
        std::process::exit(1);
    }
}
