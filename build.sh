hs_wasm_path=./Zilly.WASM
"$(wasm32-wasi-ghc --print-libdir)"/post-link.mjs \
     --input "$hs_wasm_path" --output ghc_wasm_jsffi.js
wizer --allow-wasi --wasm-bulk-memory true --init-func _initialize -o dist/bin.wasm "$hs_wasm_path"
wasm-opt ${1+"$@"} dist/bin.wasm -o dist/bin.wasm
wasm-tools strip -o dist/bin.wasm dist/bin.wasm
cp ghc_wasm_jsffi.js dist/