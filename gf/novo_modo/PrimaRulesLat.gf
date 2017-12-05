--# -path=/home/herb/src/own/GF-latin/api:/home/herb/src/own/GF-latin:.
concrete PrimaRulesLat of PrimaRules = CatLat ** PrimaRulesI with (Cat=CatLat),(Syntax=SyntaxLat),(Extra = ExtraLat) ** open ResLat in {
  lincat
    CS = AdvPos => Str ;
  lin
  --    ppartAP v2 = PastPartAP (lin VP (mkVPSlash (lin V2 v2)));
    useS s = \\ap => combineSentence s ! ap ! SOV ;
};