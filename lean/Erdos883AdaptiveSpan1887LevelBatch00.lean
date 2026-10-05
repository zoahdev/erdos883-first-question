import Erdos883AdaptiveCertificate1887Data
import Erdos883AdaptiveSpanCompactCore
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
def adaptiveNumericSpans1887_0Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 11 23407426748192386389577327143419975031910992555709285758438064326116099290095617139847619086466677276707010936248627874378951991225607795872646148126287440614014010101794956021093268116626518511487570144360427801922634060651709744721788125544804369345768377975511316309472320735756409505250995813409003790794743774354879463555136
def adaptiveNumericSpans1887_0 : List AdaptiveNumericSpan := [adaptiveNumericSpans1887_0Chunk0].flatten
def adaptiveSpanEven1887_0 := adaptiveSpanTreeOfSpans (coreEvenSpans 944 0 adaptiveNumericSpans1887_0)
def adaptiveSpanWhole1887_0 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1887_0)
theorem adaptiveSpanNumericCheck1887_0 : coreNumericSpansCheck 1841 6 480 1155 adaptiveNumericSpans1887_0 adaptiveRows1887 = true := by decide +kernel
theorem adaptiveSpanEvenCache1887_0 : adaptiveSpanEven1887_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1887_0 : adaptiveSpanEven1887_0.domainCheck 944 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1887_0 : adaptiveSpanEven1887_0.spans = coreEvenSpans 944 0 adaptiveNumericSpans1887_0 := by decide +kernel
theorem adaptiveSpanWholeCache1887_0 : adaptiveSpanWhole1887_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1887_0 : adaptiveSpanWhole1887_0.domainCheck 944 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1887_0 : adaptiveSpanWhole1887_0.spans = coreWholeSpans 0 adaptiveNumericSpans1887_0 := by decide +kernel
def adaptiveNumericSpans1887_1Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 8 11490924568898645707041009399341551559590271556753979993862236063263046378427243390216698137594315526776365353365565829506835371138319772484431467335585235939833626396052447138575532087133387913472536556364011975235572843097345430931898496
def adaptiveNumericSpans1887_1 : List AdaptiveNumericSpan := [adaptiveNumericSpans1887_1Chunk0].flatten
def adaptiveSpanEven1887_1 := adaptiveSpanTreeOfSpans (coreEvenSpans 944 0 adaptiveNumericSpans1887_1)
def adaptiveSpanWhole1887_1 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1887_1)
theorem adaptiveSpanNumericCheck1887_1 : coreNumericSpansCheck 1841 6 240 385 adaptiveNumericSpans1887_1 adaptiveRows1887 = true := by decide +kernel
theorem adaptiveSpanEvenCache1887_1 : adaptiveSpanEven1887_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1887_1 : adaptiveSpanEven1887_1.domainCheck 944 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1887_1 : adaptiveSpanEven1887_1.spans = coreEvenSpans 944 0 adaptiveNumericSpans1887_1 := by decide +kernel
theorem adaptiveSpanWholeCache1887_1 : adaptiveSpanWhole1887_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1887_1 : adaptiveSpanWhole1887_1.domainCheck 944 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1887_1 : adaptiveSpanWhole1887_1.spans = coreWholeSpans 0 adaptiveNumericSpans1887_1 := by decide +kernel
def adaptiveNumericSpans1887_2Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 8 11490924568898645707041009399341551559590271556753979993862236063263046378427243390216698137594315526776365353365565829506835371138319772484431467335585368041381288642174369672295618866240867612748294686610280469470409894086769851018248320
def adaptiveNumericSpans1887_2 : List AdaptiveNumericSpan := [adaptiveNumericSpans1887_2Chunk0].flatten
def adaptiveSpanEven1887_2 := adaptiveSpanTreeOfSpans (coreEvenSpans 944 0 adaptiveNumericSpans1887_2)
def adaptiveSpanWhole1887_2 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1887_2)
theorem adaptiveSpanNumericCheck1887_2 : coreNumericSpansCheck 1841 6 720 1001 adaptiveNumericSpans1887_2 adaptiveRows1887 = true := by decide +kernel
theorem adaptiveSpanEvenCache1887_2 : adaptiveSpanEven1887_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1887_2 : adaptiveSpanEven1887_2.domainCheck 944 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1887_2 : adaptiveSpanEven1887_2.spans = coreEvenSpans 944 0 adaptiveNumericSpans1887_2 := by decide +kernel
theorem adaptiveSpanWholeCache1887_2 : adaptiveSpanWhole1887_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1887_2 : adaptiveSpanWhole1887_2.domainCheck 944 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1887_2 : adaptiveSpanWhole1887_2.spans = coreWholeSpans 0 adaptiveNumericSpans1887_2 := by decide +kernel
def adaptiveNumericSpans1887_3Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 13 37614284559875849823802251947311132812875988609909150201940784616146989091116468914497769006202164835918964580020322050557286277494722711970989529259421146955300441593755133620758753595106146314589465486276264702670274268270637497588166101303047337902705991012919249866082941564024878661227882017598480503708664051808471300391353112947230038807627546107727064534103522529690714293596586112
def adaptiveNumericSpans1887_3 : List AdaptiveNumericSpan := [adaptiveNumericSpans1887_3Chunk0].flatten
def adaptiveSpanEven1887_3 := adaptiveSpanTreeOfSpans (coreEvenSpans 944 0 adaptiveNumericSpans1887_3)
def adaptiveSpanWhole1887_3 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1887_3)
theorem adaptiveSpanNumericCheck1887_3 : coreNumericSpansCheck 1841 6 120 143 adaptiveNumericSpans1887_3 adaptiveRows1887 = true := by decide +kernel
theorem adaptiveSpanEvenCache1887_3 : adaptiveSpanEven1887_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1887_3 : adaptiveSpanEven1887_3.domainCheck 944 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1887_3 : adaptiveSpanEven1887_3.spans = coreEvenSpans 944 0 adaptiveNumericSpans1887_3 := by decide +kernel
theorem adaptiveSpanWholeCache1887_3 : adaptiveSpanWhole1887_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1887_3 : adaptiveSpanWhole1887_3.domainCheck 944 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1887_3 : adaptiveSpanWhole1887_3.spans = coreWholeSpans 0 adaptiveNumericSpans1887_3 := by decide +kernel
def adaptiveNumericSpans1887_4Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 15 60443824866848032921174552060718791642444216537832446741012561230467880413707263190425512511183515376082646149568882387531907787586249424369780946941566915182264994961148194910150240576513135295778321887645815264119337368753072148947723911582491408724760382141031016626759385479048246738572511131132641109397506358851977047069523860957045722676397371968196246504809867293988072622793015416211704021894430529494952661817483301534719363475962637320320
def adaptiveNumericSpans1887_4 : List AdaptiveNumericSpan := [adaptiveNumericSpans1887_4Chunk0].flatten
def adaptiveSpanEven1887_4 := adaptiveSpanTreeOfSpans (coreEvenSpans 944 0 adaptiveNumericSpans1887_4)
def adaptiveSpanWhole1887_4 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1887_4)
theorem adaptiveSpanNumericCheck1887_4 : coreNumericSpansCheck 1841 6 192 221 adaptiveNumericSpans1887_4 adaptiveRows1887 = true := by decide +kernel
theorem adaptiveSpanEvenCache1887_4 : adaptiveSpanEven1887_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1887_4 : adaptiveSpanEven1887_4.domainCheck 944 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1887_4 : adaptiveSpanEven1887_4.spans = coreEvenSpans 944 0 adaptiveNumericSpans1887_4 := by decide +kernel
theorem adaptiveSpanWholeCache1887_4 : adaptiveSpanWhole1887_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1887_4 : adaptiveSpanWhole1887_4.domainCheck 944 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1887_4 : adaptiveSpanWhole1887_4.spans = coreWholeSpans 0 adaptiveNumericSpans1887_4 := by decide +kernel
def adaptiveNumericSpans1887_5Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 12 29672438567144390519497402573637482151932545122759682498856534613776295536921962912083910082667668972721395855512998372431819489983539265919055219267334526637414666966964978184050415903891751114220080532855601696092074327331742599297115374938477438421213225397843195366587198728301019271118887312786262762744768323077510117075005820802130701735050156024266880
def adaptiveNumericSpans1887_5 : List AdaptiveNumericSpan := [adaptiveNumericSpans1887_5Chunk0].flatten
def adaptiveSpanEven1887_5 := adaptiveSpanTreeOfSpans (coreEvenSpans 944 0 adaptiveNumericSpans1887_5)
def adaptiveSpanWhole1887_5 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1887_5)
theorem adaptiveSpanNumericCheck1887_5 : coreNumericSpansCheck 1841 6 288 323 adaptiveNumericSpans1887_5 adaptiveRows1887 = true := by decide +kernel
theorem adaptiveSpanEvenCache1887_5 : adaptiveSpanEven1887_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1887_5 : adaptiveSpanEven1887_5.domainCheck 944 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1887_5 : adaptiveSpanEven1887_5.spans = coreEvenSpans 944 0 adaptiveNumericSpans1887_5 := by decide +kernel
theorem adaptiveSpanWholeCache1887_5 : adaptiveSpanWhole1887_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1887_5 : adaptiveSpanWhole1887_5.domainCheck 944 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1887_5 : adaptiveSpanWhole1887_5.spans = coreWholeSpans 0 adaptiveNumericSpans1887_5 := by decide +kernel
end Erdos883Verified
