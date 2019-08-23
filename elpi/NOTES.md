# Random notes

## How to load

1. Start the docker container:
   ```
   ./Docker/docker-holelpi.sh 
   ```
2. Start OCaml:
   From the toplevel directory:
   ```
   rlwrap ocaml -I `camlp5 -where` `camlp5 -where`/gramlib.cma
   ```
3. Load hol:
   ```
   #use "make.ml";;
   ```
4. Save the status
   ```
   let core_st = get_hol_status();;
   ```
5. Load the Elpi extension:
   ```
   trace_parsed_terms := false;;
   loadt "elpi/make.ml";;
   ```
6. Change the status as needed
   ```
   unreserve_words ["^"];;
   set_hol_status core_st;;
   ```
   and follow instructions on top of trace_parsed_terms.ml.

## Manually test one entry

1. Load the trace code if necessary:
   ```
   needs "elpi/trace_parsed_terms.ml";;
   ```
2. Load the saved trace:
   ```
   let pterms = load_parsed_terms "elpi/CORE.bin";;
   ```
3. Pick a term:
   ```
   let stm,ptm,st = el 2 pterms;;
   ```
4. Run the elaborator on the string:
   ```
   let qtm = Hol_elpi.quotation stm;;
   ```
5. Also see file test_parsed_terms.ml.
