
CLaM version 3.2
================

This version runs under sicstus 4.01,
after revision 5/2008 Alan Smaill 
(no quintus or swi support).

To make, check in the Makefile (make/Makefile) that CLAMSRC is assigned
to main source directory, where this file is; and edit
the SICSTUS variable if necessary.
To build the clam executable:

   cd make
   make

This will create the saved image "clam.sic" in the "make" 
directory. You can then run this via the script clam from the make directory:

   ./clam

Or from the CLAMSRC directory, using

   make/clam

There is minimal documentation, unfortunately;
see $CLAMSRC/lemma_calc_script.n for record of a run with the system.

Further scripts are in $CLAMSRC/lib/scripts .

On-line help is available via

?- options.


Notes below from earlier release.


CLaM VERSION 3.0					      13/11/92
======================================================================

bin:
	This directory contains links to the executables for the
        Oyster proof environment (e.g. oyster.qui), version 3.0
        of the Clam proof planner (e.g. clam.v3.0.qui), the X
	version of the Clam proof planner (e.g. xclam.v3.0.qui)
	and the C executable, xclam, which provides the interface 
	between Clam and XClam.

dialect-support:

       	Directory containing the boot-strap file sub-directories
       	for the various dialects of prolog supported by the Makefile.
       	Currently only sic and qui (sictsus and quintus) are available.
       	Each sub-directory contains:

       	boot -- (bootstrap code: if/1, reload/1,
                lib_include/1, reload/1, loadc/1, time_stamp/1).
       	libs -- Library routines needed for CLaM.      

info-for-users:

	This directory contains various information of use to users
        including the Clam manual and a short introduction to the
      	Oyster-Clam proof system. The output from the clam benchmarking
        script is also written here (benchmark-results).
  
lib:

	The Clam.v3.0 library is distributed across a number of 
   	subdirectories. Clam.v3.0 should plan and prove all theorems
        in ./lib/thm which are referenced in the examples.pl file (except
        those which are tagged as being bad). The needs.pl file is 
  	used to record dependencies between definitions, theorems and 
        methods. 

lib-buffer:

	The lib_buffer provides a directory into which clam-users can
        copy definitions, theorems, lemmas etc for validation by the
        current keeper of clam before being installed in the offical
        lib directory. lib-buffer is the default library directory
        for saving objects.

low-level-code:

	Low-Level support routines. 

make:

	makefile for construction of Oyster and Clam to suit various 
  	Prolog's only sicstus and quintus have been actively maintained.

meta-level-support:

	Method support, in particular the definition of the 
        meta-logical predicates in which the preconditions
    	methods are expressed.

proof-planning:

	Proof planning support, library mechanism and planners.


________________________

Note that the following are not officially supported in version 3.0:


bmra:
	An enhanced Boyer-Moore style recursion analysis
    	(Note:  NOT CURRENTLY SUPPORTED BY CLAM.v3.0)

data-type-shell:

	Support for the introduction of recursive functions and data-types
	in oyster:

	sh -    The shell for introducing recursive functions and data-types
	        to CLaM.   The lemmas defined in mkttprims are needed for
                the functioning of this sub-system.

	ra -    The original shell for introducing recursive functions and 
		data-types in oyster from which sh was derived. It was discarded 
                because:
     	           (a) it is humoungously slow to actually run oyster proofs for
     	               all the stuff the shell does.
     	           (b) All the well-formedness witness arguments get in the way when
     		proof-planning.
     	        If ``noprove := 1'' is executed before this lot is loaded,
     	        a kind of half-way house to the sh shell is built.
     	        If ``unsound_wff_check := 1'' a much quicker but not necessarily
     	        sound wff test is used by the shell instead of proper wff proofs.
     	        Even with this option things are slooow.

	bthm -  Some ``boot-strap'' theorems loaded by the ``ra'' that it
       	        needs to operate.  The file 'ra/huttprims' contains the commands
       	        needed to load these.

	shegs - Examples I used to exercise the ``ra'' shell.

    	(Note:  NOT CURRENTLY SUPPORTED BY CLAM.v3.0)

lib-dest:

	A little library that stores the few toy destructor form
       	planning examples that were run to debug the rippling-across
        proof plan. Contains the commands used to create these examples 
    	and a needs file that patches the needs data-base to support 
	these examples. 
    	(Note:  NOT CURRENTLY SUPPORTED BY CLAM.v3.0)

x-support:

	X interface suppport. Includes both prolog and C code.
    	(Note:  NOT CURRENTLY SUPPORTED BY CLAM.v3.0)

-------------------------------------------------



Andrew Ireland 		

(air@uk.ac.ed.aisb)

