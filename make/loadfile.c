#include <stdio.h>

main( argc, argv)
    int argc;
    char *argv[];

{
    int i;
    for( i = 1 ; i < argc ; ++i ) 
    {
	if( i+1 < argc )
	    printf( "'%s',\n", argv[i] );
	else
	    printf( "'%s'\n", argv[i] );
    }
    
    exit(0);

}

