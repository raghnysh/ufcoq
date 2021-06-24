### Find duplicate labels for fragments

## Usage:
##
## This program is intended to be used with the script fragments.awk
## like this:
##
##   awk -f fragments.awk file... > fragments.csv
##   awk -f duplicates.awk fragments.csv
##
## or:
##
##   awk -f fragments.awk file... | awk -f duplicates.awk
##
## Print to standard output data about duplicate labels for fragments.
## A duplicate label is a string which occurs as a label in more than
## one fragment.
##
## Sample output:
##
##   [WARNING] Duplicate labels found:
##   aaa-bbb in foo.v (lines 2-4)
##   aaa-bbb in foo.v (lines 14-16)
##   aaa-bbb in bar.sh (lines 2-2)
##   mmm-nnn in bar.sh (lines 7-7)
##   mmm-nnn in bar.sh (lines 11-11)
##
## I assume that this script will be run with gawk although I am not
## using any special gawk features here and any POSIX compliant awk
## should do.  Just being prudent.

BEGIN {
    FS = ","
    ## Number of duplicate labels.
    duplicate_count = 0
}

{
    occurrence = sprintf("%s in %s (lines %s-%s)\n", $1, $2, $3, $4)
    occurrences[$1] = occurrences[$1] occurrence
    frequency[$1] = frequency[$1] + 1
    if (frequency[$1] == 2) {
        duplicate_count = duplicate_count + 1
        duplicates[duplicate_count] = $1
    }
}

END {
    if (duplicate_count > 0) {
        printf("[WARNING] Duplicate labels found:\n")
        for (i = 1; i <= duplicate_count; i++) {
            printf(occurrences[duplicates[i]])
        }
        exit 1
    }
}

### End of file
