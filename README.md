# minnaKanren: miniKanren For All
An optimized, extensible, and fully-featured first-order miniKanren implementation written in Chez Scheme. The goal of this repository is to serve as a platform for AI research combining symbolic and probabilistic methods.

## Installation & Use
To use this library, import it into your Scheme program with `(import mk)` and then include the source directory on your library path when you execute your script:

```scheme
scheme --libdirs aiKanren/src/mk --script myprogram.ss
```

Once you have finished developing your program, you may wish to run it using an optimized version of the library without safety checks. You can build this version with `make` using the default target and then replace the source files with the optimized binary on the library path:


```scheme
scheme --libdirs aiKanren/lib --script myprogram.ss
```

Alternatively, you may wish to compile your program together with the mk library into a single optimized binary for maximum performance. It is recommended that you run `make clean` before doing so to avoid stale binaries. You can then accomplish this with the following compilation command:
```
echo '(generate-wpo-files #t) (compile-program "myprogram.ss") (compile-whole-program "myprogram.wpo" "myprogram.so")' | scheme -q --compile-imported-libraries --libdirs src/mk --optimize-level 3
```
And then running your program with:
```
scheme --optimize-level 3 --program myprogram.so
```

## Documentation
A complete API and introduction to the various sub-libraries can be viewed [here](DOCUMENTATION.md).

## Development
Contributions are welcome. A complete list of TODO items automatically extracted from source file comments can be found [here](TODO.md). When developing or working extensively with the library, the Makefile is the primary interface to the code base. This section covers some of the functions accessible through the Makefile.

`make test` runs the tests, which can be found in the src/tests directory. 

`make bench` runs a set of benchmarks found in src/benchmarks to monitor for performance regressions. The results will be printed as well as logged to a text file in the benchmarks/ directory. Subsequent runs of `make bench` will display a comparison table between the most recent run and the immediately previous run. 

`make profile` generates a heatmap of source code performance metrics derived from running src/profile/profile.ss, which by default runs the benchmarks. The profiling output can be viewed by opening the index file that will be generated inside the profile/ directory.

`make repl` opens a command line repl with the library pre-loaded for use in experimentation.

`make doc` will automatically update the TODO and DOCUMENTATION files by extracting all source file comments that begin with TODO or DOC.

# Citation
This repository implements the paper [Goals as Constraints: Writing miniKanren Constraints in miniKanren](https://dash.harvard.edu/bitstream/handle/1/37377201/tr.pdf?sequence=1&isAllowed=y). If you use this repository in your research, please cite that paper:
```bibtex
@incollection{donahue2023constraints,
  title={Goals as Constraints: Writing miniKanren Constraints in miniKanren},
  author={Donahue, Evan},
  journal={miniKanren and Relational Programming Workshop},
  year={2023},
  booktitle={Proceedings of the 2023 miniKanren and Relational Programming Workshop},
  editor={Amin, Nada and Byrd, William E.},
  pages={1-12},
  year={2023},
  address={Cambridge},
  publisher={Harvard Technical Report}
}
```
