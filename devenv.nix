{ ... }:

{
  languages.rust = {
    channel = "stable";
    enable = true;
    components = [ "rustc" "cargo" "clippy" "rustfmt" "rust-analyzer" ];
  };
}
