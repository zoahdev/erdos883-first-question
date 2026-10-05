import Erdos883AdaptiveCertificate2085Data
import Erdos883AdaptiveSpanCompactCore
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
def adaptiveNumericSpans2085_0Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 10 20447633061427468184107240753295363981457970135580629532311365982164647043529393340397456008614131885066659534042838923762851386932048990022260551298455095431547426408984288690110048542970993544834462238646740578157722828040693169543120740260310608867692337421184327679405513150341365144656042524800
def adaptiveNumericSpans2085_0 : List AdaptiveNumericSpan := [adaptiveNumericSpans2085_0Chunk0].flatten
def adaptiveSpanEven2085_0 := adaptiveSpanTreeOfSpans (coreEvenSpans 1043 0 adaptiveNumericSpans2085_0)
def adaptiveSpanWhole2085_0 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans2085_0)
theorem adaptiveSpanNumericCheck2085_0 : coreNumericSpansCheck 2035 6 480 1155 adaptiveNumericSpans2085_0 adaptiveRows2085 = true := by decide +kernel
theorem adaptiveSpanEvenCache2085_0 : adaptiveSpanEven2085_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain2085_0 : adaptiveSpanEven2085_0.domainCheck 1043 = true := by decide +kernel
theorem adaptiveSpanEvenEntries2085_0 : adaptiveSpanEven2085_0.spans = coreEvenSpans 1043 0 adaptiveNumericSpans2085_0 := by decide +kernel
theorem adaptiveSpanWholeCache2085_0 : adaptiveSpanWhole2085_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain2085_0 : adaptiveSpanWhole2085_0.domainCheck 1043 = true := by decide +kernel
theorem adaptiveSpanWholeEntries2085_0 : adaptiveSpanWhole2085_0.spans = coreWholeSpans 0 adaptiveNumericSpans2085_0 := by decide +kernel
def adaptiveNumericSpans2085_1Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 9 16130338326464761442876179801457473541380612918257088466183211765609415207646179036352197531027851733033994287205505462804384207467364976728530825210392627533125746723162922989828550669819638153167602640785124464732126664685800159098171476705360631694787041960661090432
def adaptiveNumericSpans2085_1 : List AdaptiveNumericSpan := [adaptiveNumericSpans2085_1Chunk0].flatten
def adaptiveSpanEven2085_1 := adaptiveSpanTreeOfSpans (coreEvenSpans 1043 0 adaptiveNumericSpans2085_1)
def adaptiveSpanWhole2085_1 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans2085_1)
theorem adaptiveSpanNumericCheck2085_1 : coreNumericSpansCheck 2035 6 240 385 adaptiveNumericSpans2085_1 adaptiveRows2085 = true := by decide +kernel
theorem adaptiveSpanEvenCache2085_1 : adaptiveSpanEven2085_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain2085_1 : adaptiveSpanEven2085_1.domainCheck 1043 = true := by decide +kernel
theorem adaptiveSpanEvenEntries2085_1 : adaptiveSpanEven2085_1.spans = coreEvenSpans 1043 0 adaptiveNumericSpans2085_1 := by decide +kernel
theorem adaptiveSpanWholeCache2085_1 : adaptiveSpanWhole2085_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain2085_1 : adaptiveSpanWhole2085_1.domainCheck 1043 = true := by decide +kernel
theorem adaptiveSpanWholeEntries2085_1 : adaptiveSpanWhole2085_1.spans = coreWholeSpans 0 adaptiveNumericSpans2085_1 := by decide +kernel
def adaptiveNumericSpans2085_2Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 9 16130338326464761442876179801457473541380612918257088466183211765609415207646179036352197531027851733033994287205505462804384207467364976728530825210392627533125746723162922989828550817462542511239840521851920137520458280257707135653634662020269216624092846998671065216
def adaptiveNumericSpans2085_2 : List AdaptiveNumericSpan := [adaptiveNumericSpans2085_2Chunk0].flatten
def adaptiveSpanEven2085_2 := adaptiveSpanTreeOfSpans (coreEvenSpans 1043 0 adaptiveNumericSpans2085_2)
def adaptiveSpanWhole2085_2 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans2085_2)
theorem adaptiveSpanNumericCheck2085_2 : coreNumericSpansCheck 2035 6 720 1001 adaptiveNumericSpans2085_2 adaptiveRows2085 = true := by decide +kernel
theorem adaptiveSpanEvenCache2085_2 : adaptiveSpanEven2085_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain2085_2 : adaptiveSpanEven2085_2.domainCheck 1043 = true := by decide +kernel
theorem adaptiveSpanEvenEntries2085_2 : adaptiveSpanEven2085_2.spans = coreEvenSpans 1043 0 adaptiveNumericSpans2085_2 := by decide +kernel
theorem adaptiveSpanWholeCache2085_2 : adaptiveSpanWhole2085_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain2085_2 : adaptiveSpanWhole2085_2.domainCheck 1043 = true := by decide +kernel
theorem adaptiveSpanWholeEntries2085_2 : adaptiveSpanWhole2085_2.spans = coreWholeSpans 0 adaptiveNumericSpans2085_2 := by decide +kernel
def adaptiveNumericSpans2085_3Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 11 25920454323565117955698246357827968758379298997808738130202469535638317322714498909130200349274341411601860427903480112781109154545191682113904544009148090725212304507623075378434957487862632994657671375021449467722656666553045477384181864855018728640687027145231279237616058797616138206144989650586451668166824941666458509770880
def adaptiveNumericSpans2085_3 : List AdaptiveNumericSpan := [adaptiveNumericSpans2085_3Chunk0].flatten
def adaptiveSpanEven2085_3 := adaptiveSpanTreeOfSpans (coreEvenSpans 1043 0 adaptiveNumericSpans2085_3)
def adaptiveSpanWhole2085_3 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans2085_3)
theorem adaptiveSpanNumericCheck2085_3 : coreNumericSpansCheck 2035 6 120 143 adaptiveNumericSpans2085_3 adaptiveRows2085 = true := by decide +kernel
theorem adaptiveSpanEvenCache2085_3 : adaptiveSpanEven2085_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain2085_3 : adaptiveSpanEven2085_3.domainCheck 1043 = true := by decide +kernel
theorem adaptiveSpanEvenEntries2085_3 : adaptiveSpanEven2085_3.spans = coreEvenSpans 1043 0 adaptiveNumericSpans2085_3 := by decide +kernel
theorem adaptiveSpanWholeCache2085_3 : adaptiveSpanWhole2085_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain2085_3 : adaptiveSpanWhole2085_3.domainCheck 1043 = true := by decide +kernel
theorem adaptiveSpanWholeEntries2085_3 : adaptiveSpanWhole2085_3.spans = coreWholeSpans 0 adaptiveNumericSpans2085_3 := by decide +kernel
def adaptiveNumericSpans2085_4Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 14 52800897980036921175430210106909650028134556607015335806519893167048191441222609335771337820787559548461652230428631719282373586760465595449584430890247952390031745788475875197362606537488509921205516118339276204740516216122178745839335000665222462838007324112894171654860397611729197211300587338836410154144192802660714983792076217235077126602317465796040129312872909378310375123203937958694822174975867489123041280128
def adaptiveNumericSpans2085_4 : List AdaptiveNumericSpan := [adaptiveNumericSpans2085_4Chunk0].flatten
def adaptiveSpanEven2085_4 := adaptiveSpanTreeOfSpans (coreEvenSpans 1043 0 adaptiveNumericSpans2085_4)
def adaptiveSpanWhole2085_4 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans2085_4)
theorem adaptiveSpanNumericCheck2085_4 : coreNumericSpansCheck 2035 6 192 221 adaptiveNumericSpans2085_4 adaptiveRows2085 = true := by decide +kernel
theorem adaptiveSpanEvenCache2085_4 : adaptiveSpanEven2085_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain2085_4 : adaptiveSpanEven2085_4.domainCheck 1043 = true := by decide +kernel
theorem adaptiveSpanEvenEntries2085_4 : adaptiveSpanEven2085_4.spans = coreEvenSpans 1043 0 adaptiveNumericSpans2085_4 := by decide +kernel
theorem adaptiveSpanWholeCache2085_4 : adaptiveSpanWhole2085_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain2085_4 : adaptiveSpanWhole2085_4.domainCheck 1043 = true := by decide +kernel
theorem adaptiveSpanWholeEntries2085_4 : adaptiveSpanWhole2085_4.spans = coreWholeSpans 0 adaptiveNumericSpans2085_4 := by decide +kernel
def adaptiveNumericSpans2085_5Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 15 66933090016983308494659122851318237180621357926544912460756931822617463284967564224401617596803101795390378343864346088614256106164681789711649839454673794415748207764521395842570274454770615063478680500469602248870538746015567267672603013664381053023276801059283656923178388274756662222424840478357849780228718499633325304728448967363037385438651085759843151610737755598803537145428297926174931598266706402942599994238050569445971689192049837342848
def adaptiveNumericSpans2085_5 : List AdaptiveNumericSpan := [adaptiveNumericSpans2085_5Chunk0].flatten
def adaptiveSpanEven2085_5 := adaptiveSpanTreeOfSpans (coreEvenSpans 1043 0 adaptiveNumericSpans2085_5)
def adaptiveSpanWhole2085_5 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans2085_5)
theorem adaptiveSpanNumericCheck2085_5 : coreNumericSpansCheck 2035 6 288 323 adaptiveNumericSpans2085_5 adaptiveRows2085 = true := by decide +kernel
theorem adaptiveSpanEvenCache2085_5 : adaptiveSpanEven2085_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain2085_5 : adaptiveSpanEven2085_5.domainCheck 1043 = true := by decide +kernel
theorem adaptiveSpanEvenEntries2085_5 : adaptiveSpanEven2085_5.spans = coreEvenSpans 1043 0 adaptiveNumericSpans2085_5 := by decide +kernel
theorem adaptiveSpanWholeCache2085_5 : adaptiveSpanWhole2085_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain2085_5 : adaptiveSpanWhole2085_5.domainCheck 1043 = true := by decide +kernel
theorem adaptiveSpanWholeEntries2085_5 : adaptiveSpanWhole2085_5.spans = coreWholeSpans 0 adaptiveNumericSpans2085_5 := by decide +kernel
end Erdos883Verified
