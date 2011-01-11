
let program p =
  let filename = filename_of_module p in
  let dirname = build_path filename in
  let dir = clean_dir dirname in
    Java.print dir o
