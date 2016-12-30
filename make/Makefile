# 
# CLAMSRC should point to clam's source directory

CLAMVERSION = 3.2
CLAMSRC = ${PWD}/..
CLAMLIB = ${CLAMSRC}/lib
CLAMSYSLIB = ${CLAMSRC}/lib
CLAMSAVE = ${CLAMSRC}/lib-buffer

#  Prolog dialect to compile for
# DIA = sic - Sicstus 
# DIA = qui - Quintus
# DIA = swi - SWI
#
# Note: only sicstus supported here

DIA=sic

DIADIR= ${CLAMSRC}/dialect-support
OYSTERSRC= ${CLAMSRC}/object-level

SICSTUS=sicstus
SAVE_PROGRAM=save_program

LOWLEV =  ${CLAMSRC}/low-level/lowlev.pl \
          ${CLAMSRC}/low-level/noise.pl \
	  ${CLAMSRC}/low-level/nested_ops.pl \
	  ${CLAMSRC}/low-level/free_vars.pl \
	  ${CLAMSRC}/low-level/nuprlterm.pl \
	  ${CLAMSRC}/low-level/guess_type.pl \
          ${CLAMSRC}/low-level/instan.pl \
          ${CLAMSRC}/low-level/sub_term.pl \
	  ${CLAMSRC}/low-level/one_way.pl

PLANUTIL = ${CLAMSRC}/planner/util.pl

PLANENG = ${CLAMSRC}/planner/library.pl \
	  ${CLAMSRC}/planner/method_db.pl \
	  ${CLAMSRC}/planner/critic_db.pl \
	  ${CLAMSRC}/planner/planner.pl \
	  ${CLAMSRC}/planner/writef.pl

METAPREDS = ${CLAMSRC}/meta-level/elementary.pl \
	  ${CLAMSRC}/meta-level/reduction.pl \
	  ${CLAMSRC}/meta-level/cancellation.pl \
	  ${CLAMSRC}/meta-level/schemes.pl  \
	  ${CLAMSRC}/meta-level/recursive.pl \
	  ${CLAMSRC}/meta-level/wave_fronts.pl \
          ${CLAMSRC}/meta-level/wave_rule_parser_new.pl \
	  ${CLAMSRC}/meta-level/method_pre.pl \
	  ${CLAMSRC}/meta-level/method_con.pl \
          ${CLAMSRC}/meta-level/methodical.pl \
          ${CLAMSRC}/meta-level/critics_pre.pl \
          ${CLAMSRC}/meta-level/disprover.pl \
          ${CLAMSRC}/meta-level/wave_rule_match.pl \
          ${CLAMSRC}/meta-level/hou.pl \
          ${CLAMSRC}/meta-level/convert.pl

LAMPRO =  ${CLAMSRC}/lprolog/parameters.pl \
          ${CLAMSRC}/lprolog/library.pl \
          ${CLAMSRC}/lprolog/display.pl \
          ${CLAMSRC}/lprolog/unify.pl \
          ${CLAMSRC}/lprolog/terms.pl \
          ${CLAMSRC}/lprolog/parser.pl \
          ${CLAMSRC}/lprolog/specials.pl

LIBNEEDS = ${CLAMLIB}/needs.pl

METHODS = ${CLAMSRC}/meta-level/methods.pl \
	  ${CLAMSRC}/meta-level/critics.pl

OLDSOURCES = ${LOWLEV} ${PLANENG} ${METAPREDS} ${LAMPRO} ${LIBNEEDS} ${METHODS}
SOURCES = ${PLANUTIL} ${PLANENG} ${METAPREDS} ${LAMPRO} ${LIBNEEDS} ${METHODS}

COMPCLAM = "restore('clamlib.sic'). [makeclam]. compile_and_save_clam(clam). halt."
COMPCLAMLIB="restore('oyster.sic'). [makeclam]. compile_and_save_clam(clamlib). halt."

# easy-to-use wrappers
clam:		clam.v${CLAMVERSION}.${DIA}
	./makescript
clamlib:	clamlib.v${CLAMVERSION}.${DIA}
oyster:		oyster.${DIA}


clam.$(DIA) clam.v${CLAMVERSION}.$(DIA): loadfile makeclam.pl \
	        clamlib.v${CLAMVERSION}.$(DIA) \
                ${SOURCES}
	@rm -f clam.$(DIA) .sourcelist
	@echo 'files_to_load([' > .sourcelist
	@./loadfile $(SOURCES)  >> .sourcelist
	@echo ']).' >> ./.sourcelist	
	echo ${COMPCLAM} | ${SICSTUS}
	ln -s clam.v${CLAMVERSION}.$(DIA) clam.$(DIA)

clamlib.$(DIA) clamlib.v${CLAMVERSION}.$(DIA): loadfile makeclam.pl oyster.$(DIA) \
		                               sysdep.pl $(DIADIR)/$(DIA)/libs.pl \
		                               $(LOWLEV) 
	@rm -f clamlib.$(DIA) .sourcelist
	@echo 'files_to_load([' > .sourcelist
	@./loadfile sysdep.pl $(LOWLEV) >> .sourcelist
	@echo ']).' >> .sourcelist	
	echo ${COMPCLAMLIB} | ${SICSTUS}
	ln -s clamlib.v${CLAMVERSION}.$(DIA) clamlib.$(DIA)

oyster.sic: ${DIADIR}/sic/boot.pl ${OYSTERSRC}/sicstus.pl ${OYSTERSRC}/oyster.pl ${OYSTERSRC}/oylibs.pl
	echo "[ '${DIADIR}/sic/boot.pl', '${OYSTERSRC}/sicstus.pl']," \
	"consult( '${OYSTERSRC}/oyster.pl' ), ${SAVE_PROGRAM}('oyster.sic')." \
	| ${SICSTUS}

sysdep.pl : Makefile
	echo "?- asserta(source_dir('${CLAMSRC}'))." > sysdep.pl
	echo "?- asserta(clam_version('${CLAMVERSION}'))." >> sysdep.pl
	echo "?- asserta(lib_dir('${CLAMLIB}'))." >> sysdep.pl
	echo "?- asserta(lib_dir_system('${CLAMSYSLIB}'))." >> sysdep.pl
	echo "?- asserta(saving_dir('${CLAMSAVE}'))." >> sysdep.pl

loadfile: loadfile.c
	$(CC) -o loadfile loadfile.c

clean :
	rm -f *.nip *.swi *_hup *.sic *.o *.qui loadfile sysdep.pl
