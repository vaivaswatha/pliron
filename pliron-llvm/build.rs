fn main() {
    // Tell Cargo to link to libffi
    println!("cargo::rustc-link-lib=ffi");
}
