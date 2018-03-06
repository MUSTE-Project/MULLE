DELETE FROM Lesson WHERE Name = 'Secunda Pars';
DELETE FROM Lesson WHERE Name = 'Seconda Pars';
INSERT INTO Lesson (Name,Description,Grammar,SourceLanguage,TargetLanguage,ExerciseCount,Enabled,Repeatable)
VALUES ('Secunda Pars','Den andra Lektionen fran boken "Novo modo"','Secunda.pgf','SecundaSwe','SecundaLat',8,1,1);
DELETE FROM Exercise WHERE Lesson = 'Secunda Pars';
INSERT INTO Exercise (SourceTree,TargetTree,Lesson)
VALUES ('useS (impS they_PP (useVV nolle_VV))','useS (presS (simpleCl (usePron they_PP) (intransV gaudere_V)))','Secunda Pars'),
 ('useS (presS (simpleCl (usePron they_PP) (intransV gaudere_V)))','useS (impS they_PP (useVV nolle_VV))','Secunda Pars'),
 ('useS (impS nos_Pron (useVV velle_VV))','useS (presS (simpleCl (usePron nos_Pron) (intransV venire_V)))','Secunda Pars'),
 ('useS (presS (simpleCl (usePron nos_Pron) (intransV venire_V)))','useS (impS nos_Pron (useVV velle_VV))','Secunda Pars'),
 ('useS (pastS (simpleCl (useCNdefpl (useN Romanus_N)) (transV vincere_V2 (usePron they_PP))))','useS (pastS (simpleCl (usePron they_PP) (transV docere_V2 (useCNdefpl (useN Romanus_N)))))','Secunda Pars'),
 ('useS (pastS (simpleCl (usePron they_PP) (transV docere_V2 (useCNdefpl (useN Romanus_N)))))','useS (pastS (simpleCl (useCNdefpl (useN Romanus_N)) (transV vincere_V2 (usePron they_PP))))','Secunda Pars'),
 ('useS (pastS (simpleCl (useCNdefpl (useN vir_N)) (transV rapere_V2 (usePron they_PP))))','useS (pastS (simpleCl (usePron they_PP) (transV invitare_V2 (useCNdefpl (useN vir_N)))))','Secunda Pars'),
 ('useS (pastS (simpleCl (usePron they_PP) (transV invitare_V2 (useCNdefpl (useN vir_N)))))','useS (pastS (simpleCl (useCNdefpl (useN vir_N)) (transV rapere_V2 (usePron they_PP))))','Secunda Pars'),
 ('useS (pastS (simpleCl (useCNdefpl (useN Etruscus_N)) (transV observare_V2 (useCNindefpl (useN auspicium_N)))))','useS (pastS (simpleCl (usePron they_PP) (transV copula_V2 (useCNindefpl (useN agricola_N)))))','Secunda Pars'),
 ('useS (pastS (simpleCl (useCNdefpl (useN Romanus_N)) (transV copula_V2 (useCNindefpl (useN agricola_N)))))','useS (pastS (simpleCl (usePron they_PP) (transV observare_V2 (useCNindefpl (useN auspicium_N)))))','Secunda Pars'),
 ('useS (pastS (simpleCl (useCNdefsg (useN rex_N)) (transV observare_V2 (useCNindefpl (useN terra_N)))))','useS (pastS (simpleCl (usePron they_PP) (transV copula_V2 (useCNindefpl (useN vir_N)))))','Secunda Pars'),
 ('useS (pastS (simpleCl (useCNdefpl (useN Romanus_N)) (transV copula_V2 (useCNindefpl (useN vir_N)))))','useS (pastS (simpleCl (useCNdefsg (useN rex_N)) (transV observare_V2 (useCNindefpl (useN terra_N)))))','Secunda Pars'),
 ('useS (advS autem_Adv (pastS (simpleCl (useCNdefpl (useN Sabinus_N)) (transV habere_V2 (useCNindefpl (useN femina_N))))))','useS (advS autem_Adv (pastS (simpleCl (useCNdefpl (useN Romanus_N)) (complVA copula_VA (useA fallax_A)))))','Secunda Pars'),
 ('useS (advS autem_Adv (pastS (simpleCl (useCNdefpl (useN Romanus_N)) (complVA copula_VA (useA fallax_A)))))','useS (advS autem_Adv (pastS (simpleCl (useCNdefpl (useN Sabinus_N)) (transV habere_V2 (useCNindefpl (useN femina_N))))))','Secunda Pars'),
 ('useS (advS etiam_Adv (pastS (simpleCl (useCNdefpl (useN Sabinus_N)) (transV habere_V2 (useCNdefsg (useN religio_N))))))','useS (advS iam_Adv (pastS (simpleCl (useCNdefpl (useN Romanus_N)) (complVA copula_VA (useA victus_A)))))','Secunda Pars'),
 ('useS (advS iam_Adv (pastS (simpleCl (useCNdefpl (useN Romanus_N)) (complVA copula_VA (useA victus_A)))))','useS (advS etiam_Adv (pastS (simpleCl (useCNdefpl (useN Sabinus_N)) (transV habere_V2 (useCNdefsg (useN religio_N))))))','Secunda Pars'),
 ('useS (pastS (simpleCl (useCNdefpl (useN Sabinus_N)) (transV amare_V2 (useCNdefpl (useN liber_N)))))','useS (negPastS (simpleCl (usePron they_PP) (transV copula_V2 (useCNindefpl (attribCN (useA Romanus_A) (useN liber_N))))))','Secunda Pars'),
 ('useS (negPastS (simpleCl (useCNdefpl (useN iuvenis_N)) (transV copula_V2 (useCNindefpl (attribCN (useA Romanus_A) (useN liber_N))))))','useS (pastS (simpleCl (useCNdefpl (useN Sabinus_N)) (transV amare_V2 (useCNdefpl (useN liber_N)))))','Secunda Pars'),
 ('useS (pastS (simpleCl (useCNdefpl (useN Sabinus_N)) (transV amare_V2 (useCNdefpl (useN mulier_N)))))','useS (pastS (simpleCl (usePron they_PP) (transV copula_V2 (useCNindefpl (attribCN (useA Sabinus_A) (useN liber_N))))))','Secunda Pars'),
 ('useS (pastS (simpleCl (useCNdefpl (useN iuvenis_N)) (transV copula_V2 (useCNindefpl (attribCN (useA Sabinus_A) (useN liber_N))))))','useS (pastS (simpleCl (useCNdefpl (useN Sabinus_N)) (transV amare_V2 (useCNdefpl (useN mulier_N)))))','Secunda Pars'),
 ('useS (presS (simpleCl (useCNdefpl (useN Sabinus_N)) (transV dicere_V2 (useCNdefpl (attribCN (useA Romanus_A) (useN vir_N))))))','useS (presS (useVVCl (usePron they_PP) velle_VV (transV occidere_V2 (useCNdefpl (attribCN (useA Romanus_A) (useN vir_N))))))','Secunda Pars'),
 ('useS (presS (useVVCl (useCNdefpl (useN Sabinus_N)) velle_VV (transV occidere_V2 (useCNdefpl (attribCN (useA Romanus_A) (useN vir_N)))))))','useS (presS (simpleCl (useCNdefpl (useN Sabinus_N)) (transV dicere_V2 (useCNdefpl (attribCN (useA Romanus_A) (useN vir_N))))))','Secunda Pars'),
 ('useS (pastS (simpleCl (useCNdefpl (useN Romanus_N)) (transV contendere_V2 (usePron they_PP))))','useS (pastS (simpleCl (usePron they_PP) (transV contendere_V2 (useCNdefpl (useN Romanus_N)))))','Secunda Pars'),
 ('useS (pastS (simpleCl (useCNdefpl (useN Romanus_N)) (transV docere_V2 (usePron they_PP))))','useS (pastS (simpleCl (usePron they_PP) (transV docere_V2 (useCNdefpl (useN Romanus_N)))))','Secunda Pars')
;
