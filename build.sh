#!/bin/bash

mkdir -p build

for subject in ./sem*/*; do
    subject_base=$(basename $subject)

    for lecture in $subject/*; do
        lecture_base=$(basename $lecture)
        rel_path="${lecture#./}"

        out_dir=build/$rel_path
        mkdir -p $out_dir

        lecture_path=$lecture/$subject_base-$lecture_base.typ
        lecture_path="${lecture_path#./}"

        basename_file=$(basename $lecture_path)

        out_file="$out_dir/${basename_file%.typ}.pdf"

        echo "compiling $lecture_path -> $out_file"

        typst compile --root . $lecture_path $out_file
    done
done
