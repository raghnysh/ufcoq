### Get data about fragments in files

## Usage:
##
##   awk -f fragments.awk file...
##
## Print to standard output data about fragments in the given files.
##
## A fragment is a piece of text delimited at the top by a line
## containing a string of the form "begfrag:label", and at the bottom
## by a line containing a string of the form "endfrag".  The suffix
## label must be a string consisting of letters, digits, and the
## hyphen character.
##
## The data is printed as a CSV list with entries of the form
## "label,filename,start,end", where start is the number in the file
## of the first line of the fragment excluding the begfrag delimiter
## line, and end is the number in the file of the last line of the
## fragment excluding the endfrag delimiter line.  Blank lines
## immediately following the begfrag line, and immediately preceding
## the endfrag line, are not counted when determining start and end.
##
## This program does not check for duplicate labels.  It merely parses
## the given files, and produces data about the fragments in them.
## The output of this program can be further processed to find
## information about duplicate labels, as is done by the accompanying
## script duplicates.awk.
##
## I assume that this script will be run with gawk although I am not
## using any special gawk features here and any POSIX compliant awk
## should do.  Just being prudent.

### ==================================================================
### The line processor
### ==================================================================

BEGIN {
    initialise()
}

{
    process_line()
}

END {
    finalise()
}

### ==================================================================
### Function definitions
### ==================================================================

## Local variables are declared as parameters with names having the
## prefix "l_".

function initialise() {
    ## Regular expression that matches the opening string of a
    ## fragment start tag.
    fragment_start_tag_prefix = "^.*begfrag:"

    ## Regular expression that matches the closing string of a
    ## fragment start tag.
    fragment_start_tag_suffix = "[^[:digit:][:alpha:]-]*$"

    ## Regular expression that matches the opening string of a
    ## fragment end tag.
    fragment_end_tag_prefix = "^.*endfrag"
    ## Regular expression that matches the closing string of a
    ## fragment end tag.
    fragment_end_tag_suffix = fragment_start_tag_suffix

    ## The current number of fragments.
    fragment_count = 0

    return 0
}

function process_line() {
    if (is_fragment_start_tag_line($0))
        process_fragment_start_tag_line()

    if (is_fragment_blank_line($0))
        process_fragment_blank_line()

    if (is_fragment_end_tag_line($0))
        process_fragment_end_tag_line()

    return 0
}

function finalise(l_index, l_output) {
    for (l_index = 1; l_index <= fragment_count; l_index++)
        l_output = l_output \
            generate_fragment_data( \
                fragment_identifiers_table[l_index], \
                fragment_files_table[l_index], \
                fragment_beginnings_table[l_index], \
                fragment_endings_table[l_index] \
                )

    printf(l_output)

    return 0
}

function is_fragment_start_tag_line(string) {
    return string ~ fragment_start_tag_prefix
}

function is_fragment_blank_line(string) {
    return string ~ "^[[:space:]]*$" && in_fragment == "yes"
}

function is_fragment_end_tag_line(string) {
    return string ~ fragment_end_tag_prefix
}

function process_fragment_start_tag_line() {
    in_fragment = "yes"
    fragment_count = fragment_count + 1
    fragment_identifiers_table[fragment_count] = \
        fragment_identifier_from_string($0)
    fragment_files_table[fragment_count] = FILENAME
    fragment_beginnings_table[fragment_count] = FNR + 1

    ## https://www.gnu.org/software/gawk/manual/html_node/Delete.html
    ## https://www.austingroupbugs.net/view.php?id=544
    delete fragment_blanks_table

    return 0
}

function process_fragment_blank_line() {
    fragment_blanks_table[FNR] = fragment_identifier

    return 0
}

function process_fragment_end_tag_line(l_begin, l_end) {
    in_fragment = "no"
    fragment_endings_table[fragment_count] = FNR - 1

    l_begin = fragment_beginnings_table[fragment_count]
    while (l_begin in fragment_blanks_table)
        l_begin = l_begin + 1
    fragment_beginnings_table[fragment_count] = l_begin

    l_end = fragment_endings_table[fragment_count]
    while (l_end in fragment_blanks_table)
        l_end = l_end - 1
    fragment_endings_table[fragment_count] = l_end

    return 0
}

function fragment_identifier_from_string(string) {
    gsub(fragment_start_tag_prefix, "", string)
    gsub(fragment_start_tag_suffix, "", string)
    gsub(fragment_end_tag_prefix, "", string)
    gsub(fragment_end_tag_suffix, "", string)

    return string
}

function generate_fragment_data(identifier, file, begin, end) {
    return sprintf("%s,%s,%s,%s\n", identifier, file, begin, end)
}

### End of file
