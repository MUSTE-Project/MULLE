This contains some `.pgf-files` used for testing.  This just contains
the compiled binary and not the grammar file for them.  When we
reliably can make invoking the `gf` compiler a part of the pipeline,
perhaps we can change this.

## novo-modo-test/Prima.pgf

This binary was generated based on

    commit 99f92e45da091fa36df201ca0ba0ec271c82149e
    Author: Frederik Hanghøj Iversen <fhi.1990@gmail.com>
    Date:   Mon Aug 6 14:21:30 2018 +0200

With the patch:

    diff --git a/muste/data/gf/grammars/novo_modo/PrimaRulesLat.gf b/muste/data/gf/grammars/novo_modo/PrimaRulesLat.gf
    index 8afa4d7..7844ecb 100644
    --- a/muste/data/gf/grammars/novo_modo/PrimaRulesLat.gf
    +++ b/muste/data/gf/grammars/novo_modo/PrimaRulesLat.gf
    @@ -1,16 +1,10 @@
     --# -path=latin-rgl/api:latin-rgl:.
    -concrete PrimaRulesLat of PrimaRules = CatLat ** PrimaRulesI-[useCNdefsg,useCNindefsg,useCNindefpl]
    +concrete PrimaRulesLat of PrimaRules = CatLat ** PrimaRulesI
       with (Cat=CatLat), (Syntax=SyntaxLat), (Extra=ExtraLat), (Conjunction=ConjunctionLat) **
       open ResLat in {
    -
     lincat
       CS = Str ;
    -
    -  lin
    -    useCNdefsg cn = let q : Det = lin Det {s = \\_,_ => "" ; sp = \\_,_ => "(definite)" ; n = Sg } in lin NP (mkNP (q | theSg_Det) (lin CN cn)) ;
    -    useCNindefsg cn = let q : Det = lin Det {s = \\_,_ => "" ; sp = \\_,_ => "(indefinite)" ; n = Sg } in lin NP (mkNP (q | aSg_Det) (lin CN cn)) ;
    -    useCNindefpl cn = let q : Det = lin Det {s = \\_,_ => "" ; sp = \\_,_ => "(indefinite)" ; n = Pl } in lin NP (mkNP (q | aPl_Det) (lin CN cn));
    +lin
         --    ppartAP v2 = PastPartAP (lin VP (mkVPSlash (lin V2 v2)));
         useS s = combineSentence s ! SPreO ! PreV ! SOV ;
    -
     }
    \ No newline at end of file
