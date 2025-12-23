These are the lecture notes for COMP2012 (IFR) using lean4 and verso.

Run
lake exe cache get
lake exe lacnotes
and then 
cd _out/html-multi
python3 -m http.server 8000
open http://localhost:8000

if anchors are stuck:
rm -rf .lake/build/highlighted
