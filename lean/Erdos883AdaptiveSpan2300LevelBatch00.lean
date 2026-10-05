import Erdos883AdaptiveCertificate2300Data
import Erdos883AdaptiveSpanCompactCore
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
def adaptiveNumericSpans2300_0Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 12 35764566052282272376928925510493269351959407865560929763736588085572107589699231158952592472024375925865979463694744537563364257501358775425007054597569413468609672725840119199749530118845773737504357531203548803071382798875388255661474732840113758683692365843436383120331769164851988374404185722774517792998081371571142663264822343972953601579451281099980864
def adaptiveNumericSpans2300_0 : List AdaptiveNumericSpan := [adaptiveNumericSpans2300_0Chunk0].flatten
def adaptiveSpanEven2300_0 := adaptiveSpanTreeOfSpans (coreEvenSpans 1150 0 adaptiveNumericSpans2300_0)
def adaptiveSpanWhole2300_0 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans2300_0)
theorem adaptiveSpanNumericCheck2300_0 : coreNumericSpansCheck 2245 7 480 1155 adaptiveNumericSpans2300_0 adaptiveRows2300 = true := by decide +kernel
theorem adaptiveSpanEvenCache2300_0 : adaptiveSpanEven2300_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain2300_0 : adaptiveSpanEven2300_0.domainCheck 1150 = true := by decide +kernel
theorem adaptiveSpanEvenEntries2300_0 : adaptiveSpanEven2300_0.spans = coreEvenSpans 1150 0 adaptiveNumericSpans2300_0 := by decide +kernel
theorem adaptiveSpanWholeCache2300_0 : adaptiveSpanWhole2300_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain2300_0 : adaptiveSpanWhole2300_0.domainCheck 1150 = true := by decide +kernel
theorem adaptiveSpanWholeEntries2300_0 : adaptiveSpanWhole2300_0.spans = coreWholeSpans 0 adaptiveNumericSpans2300_0 := by decide +kernel
def adaptiveNumericSpans2300_1Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 9 17557159749646781263464386614088732298446461159298587905394106781396794591102550424133660838108055633570939539623080622516420118233038153226337643579919692003303364006553070785798854516879671187530999632439502323223513523557428437764226679173948108810406593429210398848
def adaptiveNumericSpans2300_1 : List AdaptiveNumericSpan := [adaptiveNumericSpans2300_1Chunk0].flatten
def adaptiveSpanEven2300_1 := adaptiveSpanTreeOfSpans (coreEvenSpans 1150 0 adaptiveNumericSpans2300_1)
def adaptiveSpanWhole2300_1 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans2300_1)
theorem adaptiveSpanNumericCheck2300_1 : coreNumericSpansCheck 2245 7 240 385 adaptiveNumericSpans2300_1 adaptiveRows2300 = true := by decide +kernel
theorem adaptiveSpanEvenCache2300_1 : adaptiveSpanEven2300_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain2300_1 : adaptiveSpanEven2300_1.domainCheck 1150 = true := by decide +kernel
theorem adaptiveSpanEvenEntries2300_1 : adaptiveSpanEven2300_1.spans = coreEvenSpans 1150 0 adaptiveNumericSpans2300_1 := by decide +kernel
theorem adaptiveSpanWholeCache2300_1 : adaptiveSpanWhole2300_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain2300_1 : adaptiveSpanWhole2300_1.domainCheck 1150 = true := by decide +kernel
theorem adaptiveSpanWholeEntries2300_1 : adaptiveSpanWhole2300_1.spans = coreWholeSpans 0 adaptiveNumericSpans2300_1 := by decide +kernel
def adaptiveNumericSpans2300_2Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 10 22256344094942652118343280144268096030494825079424920452304802118643150721615889758390871054428996991343998806637006791758325111396493335084513677726668629270237992771501453398987584094489774750476348929484146615598450098687579687345436336509619998060783664809197158336667050937522596679564428050560
def adaptiveNumericSpans2300_2 : List AdaptiveNumericSpan := [adaptiveNumericSpans2300_2Chunk0].flatten
def adaptiveSpanEven2300_2 := adaptiveSpanTreeOfSpans (coreEvenSpans 1150 0 adaptiveNumericSpans2300_2)
def adaptiveSpanWhole2300_2 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans2300_2)
theorem adaptiveSpanNumericCheck2300_2 : coreNumericSpansCheck 2245 7 720 1001 adaptiveNumericSpans2300_2 adaptiveRows2300 = true := by decide +kernel
theorem adaptiveSpanEvenCache2300_2 : adaptiveSpanEven2300_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain2300_2 : adaptiveSpanEven2300_2.domainCheck 1150 = true := by decide +kernel
theorem adaptiveSpanEvenEntries2300_2 : adaptiveSpanEven2300_2.spans = coreEvenSpans 1150 0 adaptiveNumericSpans2300_2 := by decide +kernel
theorem adaptiveSpanWholeCache2300_2 : adaptiveSpanWhole2300_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain2300_2 : adaptiveSpanWhole2300_2.domainCheck 1150 = true := by decide +kernel
theorem adaptiveSpanWholeEntries2300_2 : adaptiveSpanWhole2300_2.spans = coreWholeSpans 0 adaptiveNumericSpans2300_2 := by decide +kernel
def adaptiveNumericSpans2300_3Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 14 57471441825825951325776687436748095945408030209404874654893399402335395276687214368384473539614014602323988067693780877845401846996920116490103839919093622449643495199273798238183740316097932188901381883510789519740972919886164883792942358318919972379377374684836581110657586528213337505535024630784323719165150566800534853245147829460153350862606455134645545633869413306761716222127886904005297574586675809854737612928
def adaptiveNumericSpans2300_3 : List AdaptiveNumericSpan := [adaptiveNumericSpans2300_3Chunk0].flatten
def adaptiveSpanEven2300_3 := adaptiveSpanTreeOfSpans (coreEvenSpans 1150 0 adaptiveNumericSpans2300_3)
def adaptiveSpanWhole2300_3 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans2300_3)
theorem adaptiveSpanNumericCheck2300_3 : coreNumericSpansCheck 2245 7 120 143 adaptiveNumericSpans2300_3 adaptiveRows2300 = true := by decide +kernel
theorem adaptiveSpanEvenCache2300_3 : adaptiveSpanEven2300_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain2300_3 : adaptiveSpanEven2300_3.domainCheck 1150 = true := by decide +kernel
theorem adaptiveSpanEvenEntries2300_3 : adaptiveSpanEven2300_3.spans = coreEvenSpans 1150 0 adaptiveNumericSpans2300_3 := by decide +kernel
theorem adaptiveSpanWholeCache2300_3 : adaptiveSpanWhole2300_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain2300_3 : adaptiveSpanWhole2300_3.domainCheck 1150 = true := by decide +kernel
theorem adaptiveSpanWholeEntries2300_3 : adaptiveSpanWhole2300_3.spans = coreWholeSpans 0 adaptiveNumericSpans2300_3 := by decide +kernel
def adaptiveNumericSpans2300_4Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 16 92353046328337087462147304988194916759481023701158959900682685150152515737702685548192882427099408375993241057645488194892689461116044170348776641022214620252324679218355448368171357062355381189517143462834696495117311892181588323593972621662913524627097319204727892033828936975757922256313849344683035264922451614956926351749423470817034318737365750014446519287494956292425935815775179140252733221713748321376725368662539730447192291305391144303569464423848488405017270606102656
def adaptiveNumericSpans2300_4 : List AdaptiveNumericSpan := [adaptiveNumericSpans2300_4Chunk0].flatten
def adaptiveSpanEven2300_4 := adaptiveSpanTreeOfSpans (coreEvenSpans 1150 0 adaptiveNumericSpans2300_4)
def adaptiveSpanWhole2300_4 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans2300_4)
theorem adaptiveSpanNumericCheck2300_4 : coreNumericSpansCheck 2245 7 192 221 adaptiveNumericSpans2300_4 adaptiveRows2300 = true := by decide +kernel
theorem adaptiveSpanEvenCache2300_4 : adaptiveSpanEven2300_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain2300_4 : adaptiveSpanEven2300_4.domainCheck 1150 = true := by decide +kernel
theorem adaptiveSpanEvenEntries2300_4 : adaptiveSpanEven2300_4.spans = coreEvenSpans 1150 0 adaptiveNumericSpans2300_4 := by decide +kernel
theorem adaptiveSpanWholeCache2300_4 : adaptiveSpanWhole2300_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain2300_4 : adaptiveSpanWhole2300_4.domainCheck 1150 = true := by decide +kernel
theorem adaptiveSpanWholeEntries2300_4 : adaptiveSpanWhole2300_4.spans = coreWholeSpans 0 adaptiveNumericSpans2300_4 := by decide +kernel
def adaptiveNumericSpans2300_5Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 29 2015791403040311547055357118262414662631641618117231102839046034866356270176538967531532783790788976913154557110141747281776542211781951670666040165903286073698149315520399610986637490103623561674844108335835670016225979457704935888159817620243513596889998437200736171229686285629688759243216319445447526956660903059938625884968245857452044933841723315275881708671498881193531386663123462971285302638954397793064415247602624870177945597824808600183278622936574548532209231795405015352789226815586798055099774029409390258835974761129908146986665429081359211247176740338890939321588995055807162474253875485951958738048129759224586393063208525349131632247216270081855274441775012321291651891462892081012312796450857319490898086831379857058179900185116969079108192714167829706595166012509266474995394299276662278757767436783395172151025953250572310410866493949209607478968448
def adaptiveNumericSpans2300_5 : List AdaptiveNumericSpan := [adaptiveNumericSpans2300_5Chunk0].flatten
def adaptiveSpanEven2300_5 := adaptiveSpanTreeOfSpans (coreEvenSpans 1150 0 adaptiveNumericSpans2300_5)
def adaptiveSpanWhole2300_5 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans2300_5)
theorem adaptiveSpanNumericCheck2300_5 : coreNumericSpansCheck 2245 7 288 323 adaptiveNumericSpans2300_5 adaptiveRows2300 = true := by decide +kernel
theorem adaptiveSpanEvenCache2300_5 : adaptiveSpanEven2300_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain2300_5 : adaptiveSpanEven2300_5.domainCheck 1150 = true := by decide +kernel
theorem adaptiveSpanEvenEntries2300_5 : adaptiveSpanEven2300_5.spans = coreEvenSpans 1150 0 adaptiveNumericSpans2300_5 := by decide +kernel
theorem adaptiveSpanWholeCache2300_5 : adaptiveSpanWhole2300_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain2300_5 : adaptiveSpanWhole2300_5.domainCheck 1150 = true := by decide +kernel
theorem adaptiveSpanWholeEntries2300_5 : adaptiveSpanWhole2300_5.spans = coreWholeSpans 0 adaptiveNumericSpans2300_5 := by decide +kernel
end Erdos883Verified
