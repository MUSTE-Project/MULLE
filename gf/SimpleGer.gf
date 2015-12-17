concrete SimpleGer of Simple = open Prelude in {
  param
    Number = Sg | Pl ;
    Case = Nom | Akk ;
    Gender = Fem | Masc | Neutr ;
  lincat
    S = SS ;
    N,AP = { s : Number => Case => Str ; g : Gender } ;
    NP = { s : Case => Str ; n : Number } ;
    Det = { s : Gender => Case => Str ; n : Number } ;
    V , VP , A = { s : Number => Str } ;
  lin
    -- Lexicon
    defSg_Det =
      mkDetSg "der" "die" "das" "den" ;
    defPl_Det =
      { s = \\_,_ => "die" ; n = Pl } ;
    indefSg_Det =
      mkDetSg "eine" "ein" "ein" "einen" ;
    indefPl_Det =
      { s = \\_,_ => "" ; n = Pl } ;
    bread_N = mkNoun Neutr "Brot" "Brote" ;
    man_N = mkNoun Masc "Mann" "Männer" ;
    woman_N = mkNoun Fem "Frau" "Frauen" ;
    eat_V = { s = table { Sg => "isst" ; Pl => "essen" } } ;
    old_A = { s = table { Sg => "alte" ; Pl => "alten" } } ;
    -- Syntax rules
    mkAP a n = { s = \\num,cas => a.s ! num ++ n.s ! num ! cas ; g = n.g } ;
    mkNP1 det ap = { s = \\cas => det.s ! ap.g ! cas ++ ap.s ! det.n ! cas ; n = det.n } ;
    mkNP2 det n = { s = \\cas => det.s ! n.g ! cas ++ n.s ! det.n ! cas ; n = det.n } ;
    mkVP1 v = v ;
    mkVP2 v np = { s = \\n => v.s ! n ++ np.s ! Akk } ;
    mkS np vp = { s = np.s ! Nom ++ vp.s ! np.n } ;
  oper
    mkDetSg : Str -> Str -> Str -> Str -> Det = \masc,fem,neutr,mascAkk ->
      lin Det { s = \\g,c =>
	  case <g,c> of {
	    <Fem,Nom|Akk> => fem ;
	    <Masc,Nom> => masc ;
	    <Masc,Akk> => mascAkk ;
	    <Neutr,Nom|Akk> => neutr 
		  } ;
		n = Sg ;
      };
    mkNoun : Gender -> Str -> Str -> N = \g,sg,pl ->
      lin N { g = g ;
	s = \\n,c =>
	  case <n,c> of {
	    <Sg,Nom|Akk> => sg ;
	    <Pl,Nom|Akk> => pl
	  }
      };
}