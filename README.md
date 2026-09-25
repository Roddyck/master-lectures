## UNN math masters program lectures

This is a collection of lecture notes for math masters program at University of Nizhni Novgorod.

The lectures are written in [Typst](https://typst.app/).

### Releases

Latest zipped pdfs are available in the [releases](https://github.com/Roddyck/master-lectures/releases/tag/latest)

Or see specific [tagged releases](https://github.com/Roddyck/master-lectures/releases).

### Build

To build the lectures, you need to have [Typst](https://typst.app/) installed.

Then either run `build.sh` script that creates a `build` directory in the root
mirroring the structure of root.

```bash
./build.sh
```

Or run
```bash
typst compile <lecture-filename>.typ [output-filename]
```
to compile a single lecture.
