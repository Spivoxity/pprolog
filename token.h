typedef union {
	tree E;
	type T;
	ident I;
	literal L;
} YYSTYPE;
#define	IDENT	258
#define	MONOP	259
#define	MULOP	260
#define	ADDOP	261
#define	RELOP	262
#define	WRITE	263
#define	NUMBER	264
#define	STRING	265
#define	CHAR	266
#define	ASSIGN	267
#define	DOTDOT	268
#define	NEQ	269
#define	GEQ	270
#define	LEQ	271
#define	AND	272
#define	ARRAY	273
#define	BEGN	274
#define	CASE	275
#define	CONST	276
#define	DIV	277
#define	DO	278
#define	DOWNTO	279
#define	IF	280
#define	ELSE	281
#define	END	282
#define	FOR	283
#define	FORWARD	284
#define	FUNC	285
#define	GOTO	286
#define	LABEL	287
#define	MOD	288
#define	NOT	289
#define	OF	290
#define	OR	291
#define	PROC	292
#define	PROGRAM	293
#define	RECORD	294
#define	REPEAT	295
#define	SHL	296
#define	SHR	297
#define	THEN	298
#define	TO	299
#define	TYPE	300
#define	UNTIL	301
#define	VAR	302
#define	WHILE	303
#define	CALL	304
#define	CONS	305
#define	SUB	306
#define	DOT	307
#define	FIELD	308
#define	RANGE	309
#define	PRIMTYPE	310
#define	CPARAM	311
#define	VPARAM	312
#define	NEG	313
#define	BITAND	314
#define	BITOR	315
#define	LIBCALL	316
#define	APARAM	317
#define	POINTER	318
#define	ADDRESS	319
#define	BUILTIN	320
#define	UMINUS	321
#define	N_TOKENS	322


extern YYSTYPE yylval;
