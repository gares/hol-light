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
3. Load hol and save the status:
   ```
   #use "make.ml";;
   let core_st = get_hol_status();;
   ```
4. Load the Elpi extension:
   ```
   trace_parsed_terms := false;;
   loadt "elpi/make.ml";;
   ```
5. Change the status as needed, e.g.:
   ```
   trace_parsed_terms := false;;
   trace_parsed_terms := true;;
   reserve_words ["^"];;
   unreserve_words ["^"];;
   type_invention_warning := false;;
   type_invention_warning := true;;
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