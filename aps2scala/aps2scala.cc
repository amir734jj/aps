extern "C" {
#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include "/usr/include/string.h"
#include <strings.h>
#include "aps-ag.h"
}
#include <iostream>
#include <fstream>
#include "dump-cpp.h"

using namespace std;

extern "C" {

int callset_AI(Declaration module, STATE *s) { return 0; }

static char* argv0 = "apscpp";
void usage() {
  fprintf(stderr,"%s: usage: %s [-SV] [-D...] <file.aps>\n",argv0,argv0);
  fprintf(stderr,"             compile APS to Java\n");
  /*fprintf(stderr,"    -I    generate an incremental implementation\n");*/
  fprintf(stderr,"    -S    generate a scheduled implementation\n");
  fprintf(stderr,"    -D... turn on indicated debugging flags\n");
  fprintf(stderr,"    -DH   list debugging flags\n");
  fprintf(stderr,"    -V    increase verbosity of generation code\n");
  exit(1);
}

extern void init_lexer(FILE*);
extern int aps_yyparse(void);
}

int main(int argc,char **argv) {
  argv0 = argv[0];
  if (argc < 2) usage();
  for (int i=1; i < argc; ++i) {
    if (streq(argv[i],"--omit")) {
      omit_declaration(argv[++i]);
      continue;
    } else if (streq(argv[i],"--impl")) {
      impl_module(argv[i+1],argv[i+2]);
      i += 2;
      continue;
    } else if (streq(argv[i],"-I") || streq(argv[i],"--incremental")) {
      incremental = true;
      continue;
    } else if (streq(argv[i],"-S") || streq(argv[i],"--static")) {
      static_schedule = true;
      continue;
    } else if (streq(argv[i],"-V") || streq(argv[i],"--verbose")) {
      ++verbose;
      continue;
    } else if (argv[i][0] == '-' && argv[i][1] == 'D') {
      set_debug_flags(argv[i]+2);
      continue;
    } else if (argv[i][0] == '-') {
      usage();
    }
    Program p = find_Program(make_string(argv[i]));
    if (p == 0) {
      fprintf(stderr,"Cannot find APS compilation unit %s\n",argv[i]);
      continue;
    }
    aps_check_error("parse");
    aps_yyfilename = (char*)program_name(p);
    bind_Program(p);
    aps_check_error("binding");
    type_Program(p);
    aps_check_error("type");
    if (static_schedule) {
      analyze_Program(p);
      aps_check_error("analysis");
      cerr << "Warning: static scheduling not implemented: reverting to dynamic..." << endl;
      static_schedule = 0;
    }
    char* hfilename = str2cat(argv[i],".h");
    char* cppfilename = str2cat(argv[i],".cpp");

    cout << "hfile = " << hfilename << ", cppfile = " << cppfilename << endl;
    ofstream header(hfilename);
    ofstream body(cppfilename);
    dump_cpp_Program(p,header,body);
  }
  exit(0);
}



