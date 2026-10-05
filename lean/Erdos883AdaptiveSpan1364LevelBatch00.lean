import Erdos883AdaptiveCertificate1364Data
import Erdos883AdaptiveSpanCompactCore
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
def adaptiveNumericSpans1364_0Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 8 8266852182797039286205617734509149284879282881751223378856303647641706598679803841457896063644201338259101812025093438008497089724464965025699264341770597764638255880145574371256980440852124762503453854129812706657207182053506123164549184
def adaptiveNumericSpans1364_0 : List AdaptiveNumericSpan := [adaptiveNumericSpans1364_0Chunk0].flatten
def adaptiveSpanEven1364_0 := adaptiveSpanTreeOfSpans (coreEvenSpans 682 0 adaptiveNumericSpans1364_0)
def adaptiveSpanWhole1364_0 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1364_0)
theorem adaptiveSpanNumericCheck1364_0 : coreNumericSpansCheck 1334 6 480 1155 adaptiveNumericSpans1364_0 adaptiveRows1364 = true := by decide +kernel
theorem adaptiveSpanEvenCache1364_0 : adaptiveSpanEven1364_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1364_0 : adaptiveSpanEven1364_0.domainCheck 682 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1364_0 : adaptiveSpanEven1364_0.spans = coreEvenSpans 682 0 adaptiveNumericSpans1364_0 := by decide +kernel
theorem adaptiveSpanWholeCache1364_0 : adaptiveSpanWhole1364_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1364_0 : adaptiveSpanWhole1364_0.domainCheck 682 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1364_0 : adaptiveSpanWhole1364_0.spans = coreWholeSpans 0 adaptiveNumericSpans1364_0 := by decide +kernel
def adaptiveNumericSpans1364_1Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 6 5144474743336570326982820920799654344210950115523785541131818421560920000738354982244590705654160747093069958705121342822114581067695041647774669663395325974206490278029974044800
def adaptiveNumericSpans1364_1 : List AdaptiveNumericSpan := [adaptiveNumericSpans1364_1Chunk0].flatten
def adaptiveSpanEven1364_1 := adaptiveSpanTreeOfSpans (coreEvenSpans 682 0 adaptiveNumericSpans1364_1)
def adaptiveSpanWhole1364_1 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1364_1)
theorem adaptiveSpanNumericCheck1364_1 : coreNumericSpansCheck 1334 6 240 385 adaptiveNumericSpans1364_1 adaptiveRows1364 = true := by decide +kernel
theorem adaptiveSpanEvenCache1364_1 : adaptiveSpanEven1364_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1364_1 : adaptiveSpanEven1364_1.domainCheck 682 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1364_1 : adaptiveSpanEven1364_1.spans = coreEvenSpans 682 0 adaptiveNumericSpans1364_1 := by decide +kernel
theorem adaptiveSpanWholeCache1364_1 : adaptiveSpanWhole1364_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1364_1 : adaptiveSpanWhole1364_1.domainCheck 682 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1364_1 : adaptiveSpanWhole1364_1.spans = coreWholeSpans 0 adaptiveNumericSpans1364_1 := by decide +kernel
def adaptiveNumericSpans1364_2Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 6 5144474743336570326982820920799654344210950115523785541131818421560920000738354982244590705654160747093069958705121342822204998348451178210344899684107803270628054931887427158144
def adaptiveNumericSpans1364_2 : List AdaptiveNumericSpan := [adaptiveNumericSpans1364_2Chunk0].flatten
def adaptiveSpanEven1364_2 := adaptiveSpanTreeOfSpans (coreEvenSpans 682 0 adaptiveNumericSpans1364_2)
def adaptiveSpanWhole1364_2 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1364_2)
theorem adaptiveSpanNumericCheck1364_2 : coreNumericSpansCheck 1334 6 720 1001 adaptiveNumericSpans1364_2 adaptiveRows1364 = true := by decide +kernel
theorem adaptiveSpanEvenCache1364_2 : adaptiveSpanEven1364_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1364_2 : adaptiveSpanEven1364_2.domainCheck 682 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1364_2 : adaptiveSpanEven1364_2.spans = coreEvenSpans 682 0 adaptiveNumericSpans1364_2 := by decide +kernel
theorem adaptiveSpanWholeCache1364_2 : adaptiveSpanWhole1364_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1364_2 : adaptiveSpanWhole1364_2.domainCheck 682 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1364_2 : adaptiveSpanWhole1364_2.spans = coreWholeSpans 0 adaptiveNumericSpans1364_2 := by decide +kernel
def adaptiveNumericSpans1364_3Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 9 10479480131520715255323605802950211193549723432278090276151294152070847229903109553827642372595451943351692829436117895958319111631732055114068018513131492421266835491276608426233170566362717713849286688154479907962783162262169894382237398605498839331031019100311650368
def adaptiveNumericSpans1364_3 : List AdaptiveNumericSpan := [adaptiveNumericSpans1364_3Chunk0].flatten
def adaptiveSpanEven1364_3 := adaptiveSpanTreeOfSpans (coreEvenSpans 682 0 adaptiveNumericSpans1364_3)
def adaptiveSpanWhole1364_3 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1364_3)
theorem adaptiveSpanNumericCheck1364_3 : coreNumericSpansCheck 1334 6 120 143 adaptiveNumericSpans1364_3 adaptiveRows1364 = true := by decide +kernel
theorem adaptiveSpanEvenCache1364_3 : adaptiveSpanEven1364_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1364_3 : adaptiveSpanEven1364_3.domainCheck 682 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1364_3 : adaptiveSpanEven1364_3.spans = coreEvenSpans 682 0 adaptiveNumericSpans1364_3 := by decide +kernel
theorem adaptiveSpanWholeCache1364_3 : adaptiveSpanWhole1364_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1364_3 : adaptiveSpanWhole1364_3.domainCheck 682 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1364_3 : adaptiveSpanWhole1364_3.spans = coreWholeSpans 0 adaptiveNumericSpans1364_3 := by decide +kernel
def adaptiveNumericSpans1364_4Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 16 55123489669374985313510364814120356262524980314395506958398921493550758441371664307460577912531800211892333570456307441195735398064224694733778654492293603917440618434352842392634325539139187401489616887417747796274249042445513793545480677978511401141396606539425932604421109176507541751911242268291855695595335406688872987502753444073696962262638787745623137989662271109368312754801388702508287422986080723876192215478147493545735946667279149500205572151600910397977526817259584
def adaptiveNumericSpans1364_4 : List AdaptiveNumericSpan := [adaptiveNumericSpans1364_4Chunk0].flatten
def adaptiveSpanEven1364_4 := adaptiveSpanTreeOfSpans (coreEvenSpans 682 0 adaptiveNumericSpans1364_4)
def adaptiveSpanWhole1364_4 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1364_4)
theorem adaptiveSpanNumericCheck1364_4 : coreNumericSpansCheck 1334 6 192 221 adaptiveNumericSpans1364_4 adaptiveRows1364 = true := by decide +kernel
theorem adaptiveSpanEvenCache1364_4 : adaptiveSpanEven1364_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1364_4 : adaptiveSpanEven1364_4.domainCheck 682 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1364_4 : adaptiveSpanEven1364_4.spans = coreEvenSpans 682 0 adaptiveNumericSpans1364_4 := by decide +kernel
theorem adaptiveSpanWholeCache1364_4 : adaptiveSpanWhole1364_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1364_4 : adaptiveSpanWhole1364_4.domainCheck 682 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1364_4 : adaptiveSpanWhole1364_4.spans = coreWholeSpans 0 adaptiveNumericSpans1364_4 := by decide +kernel
def adaptiveNumericSpans1364_5Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 25 465943010071106315762068170973980703791018285998121767783353499638815305515903474833080868464468427438086987113664916935663117247637090740690873048585606832635638405616838939104226212804615242339543277443252710146674726787860584895894610357633195685523936471778097825603726910197745240882895585890889861779241361481827753738402675426550500447543400903799598011172576384620970914198377678436494647932971346479315577022114791816229755212311258923923257625249998136472768828841805722750437489316388239193048766777266647371026546460530210056881703053440186954070442205837136257397659411080355340046471723868760662509891241973950099647059041356629506960016686309669547507697445991868176569973874365210751262224086508577403117887132687114951110075359428672
def adaptiveNumericSpans1364_5 : List AdaptiveNumericSpan := [adaptiveNumericSpans1364_5Chunk0].flatten
def adaptiveSpanEven1364_5 := adaptiveSpanTreeOfSpans (coreEvenSpans 682 0 adaptiveNumericSpans1364_5)
def adaptiveSpanWhole1364_5 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1364_5)
theorem adaptiveSpanNumericCheck1364_5 : coreNumericSpansCheck 1334 6 288 323 adaptiveNumericSpans1364_5 adaptiveRows1364 = true := by decide +kernel
theorem adaptiveSpanEvenCache1364_5 : adaptiveSpanEven1364_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1364_5 : adaptiveSpanEven1364_5.domainCheck 682 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1364_5 : adaptiveSpanEven1364_5.spans = coreEvenSpans 682 0 adaptiveNumericSpans1364_5 := by decide +kernel
theorem adaptiveSpanWholeCache1364_5 : adaptiveSpanWhole1364_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1364_5 : adaptiveSpanWhole1364_5.domainCheck 682 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1364_5 : adaptiveSpanWhole1364_5.spans = coreWholeSpans 0 adaptiveNumericSpans1364_5 := by decide +kernel
end Erdos883Verified
