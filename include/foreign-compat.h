-- This macro allows you to define a 'foreign import javascript' for GHCJS that
-- will be a typed stub with a meaningful error in GHC.
--
-- NOTE: You should use this macro in a single line, not across multiple lines.
-- That is, write FOREIGN_IMPORT(A, B, C, D) all on one line. Some CPPs like the
-- one used by clang will fail if the macro application spans multiple lines.

#ifdef ghcjs_HOST_OS
#define FOREIGN_IMPORT(safety,name,type,str) \
  ;foreign import javascript safety str name :: type
#else
#define FOREIGN_IMPORT(safety,name,type,str) \
  ;name :: type \
  ;name = error "'name' (a foreign import) is not defined. This is a stub to support type-checking in GHCi."
#endif
