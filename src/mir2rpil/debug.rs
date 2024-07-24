use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;

use super::rpil::RpilInst;

pub fn prepare_func_mir_log_dir() {
    use std::fs;
    use std::path::PathBuf;

    let crate_root = std::env::var("CARGO_MANIFEST_DIR").expect("Failed to get CARGO_MANIFEST_DIR");
    let log_dir = PathBuf::from(crate_root).join("playground").join("mir");
    fs::create_dir_all(&log_dir).unwrap();

    // If the directory already existed, clean it
    if log_dir.is_dir() {
        for entry in fs::read_dir(&log_dir).unwrap() {
            let entry = entry.unwrap();
            let path = entry.path();
            if path.is_file() {
                fs::remove_file(path).unwrap();
            }
        }
    }
}

pub fn log_func_mir<'tcx>(tcx: TyCtxt<'tcx>, func_id: DefId) {
    use std::fs::File;
    use std::io::Write;
    use std::path::PathBuf;

    let crate_root = std::env::var("CARGO_MANIFEST_DIR").expect("Failed to get CARGO_MANIFEST_DIR");
    let log_dir = PathBuf::from(crate_root).join("playground").join("mir");

    let debug_output = if !tcx.is_mir_available(func_id) {
        "(empty)\n".into()
    } else {
        let mir_body = tcx.optimized_mir(func_id);
        format!("{:?}\n{:#?}\n\n", func_id, mir_body)
    };
    let func_def_path = tcx.def_path_str(func_id);
    let func_id = func_id.index.as_u32();

    let log_path = log_dir.join(format!("{}.{}.log", func_def_path, func_id));
    let mut file = File::create(&log_path)
        .unwrap_or_else(|_| panic!("Failed to open `{}`", log_path.display()));
    writeln!(file, "{}", debug_output)
        .unwrap_or_else(|_| panic!("Failed to write to `{}`", log_path.display()));
}

pub fn print_func_rpil_insts<'tcx>(tcx: TyCtxt<'tcx>, func_id: DefId, rpil_insts: &Vec<RpilInst>) {
    let fn_name = tcx.def_path_str(func_id);
    let fn_id = func_id.index.as_u32();
    println!("[RPIL] `{}` {}:", fn_name, fn_id);
    if !rpil_insts.is_empty() {
        for inst in rpil_insts {
            println!("    {:?}", inst);
        }
    } else {
        println!("    (empty)");
    }
}
