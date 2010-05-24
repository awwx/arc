Michael Arntzenius's port of the Arc compiler to Arc, with the
additional step of having the original Arc compiler ac.scm (written in
Scheme) to also use the extracted Arc runtime ar.scm.

To initialize:

    mzscheme -f boot.scm

this compiles Arc and the Arc compiler (arc.arc and ac.arc) to Scheme using the original Arc compiler written in Scheme.

then, whenever you want to run Arc using the Arc compiler written in Arc:

    mzscheme -f run.scm

You'll need to run "boot.scm" again if you make changes to ac.arc, but otherwise you only need to run it once.
