### Compiling the Project 
In order to compile the project we require an active opam switch with Rocq Version >= 8.19 (compatibility with earlier versions is likely but not tested for). 

#### Install Hahn Dependency 
opam repo add coq-weakmemory-local git+https://github.com/weakmemory/local-coq-opam-archive 
opam repo add coq-promising-local git+https://github.com/weakmemory/local-coq-opam-archive 

#### Create MakeFile 
coq_makefile -f _CoqProject -o Makefile 

#### Make 
make 
