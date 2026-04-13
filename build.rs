fn main() {
    if std::env::var("CARGO_CFG_TARGET_OS").unwrap() == "windows" {
        println!("cargo:rerun-if-changed=ddc_check.rc");
        println!("cargo:rerun-if-changed=ddc_check.exe.manifest");
        println!("cargo:rerun-if-changed=icon.ico");
        embed_resource::compile("ddc_check.rc", std::iter::empty::<&str>());
    }
}
