// NOTE: For some reason on Mac you can't split the foreign import macro
// across multiple lines.
#ifdef ghcjs_HOST_OS
#define FOREIGN_IMPORT(safety,name,type,str) \
  ;foreign import javascript safety str name :: type
#else
#define FOREIGN_IMPORT(safety,name,type,str) \
  ;name :: type \
  ;name = error "'name' (a foreign import) is not defined. This is a stub to support type-checking in GHCi."
#endif
