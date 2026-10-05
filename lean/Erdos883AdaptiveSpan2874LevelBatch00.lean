import Erdos883AdaptiveCertificate2874Data
import Erdos883AdaptiveSpanCompactCore
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
def adaptiveNumericSpans2874_0Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 13 55620015534765378514672422186777485872767636656380514395912943077439586218049793791436826146208421027005955914900954179575624667026055775026772461250698134065806390584239235898550689640423604223505483745554498789405520010435176316069528870390079562810758067924975796647187129560348651988983803033578427895263341992878055185074743363839928542743841354950720502048374459232866401951577800832
def adaptiveNumericSpans2874_0 : List AdaptiveNumericSpan := [adaptiveNumericSpans2874_0Chunk0].flatten
def adaptiveSpanEven2874_0 := adaptiveSpanTreeOfSpans (coreEvenSpans 1437 0 adaptiveNumericSpans2874_0)
def adaptiveSpanWhole2874_0 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans2874_0)
theorem adaptiveSpanNumericCheck2874_0 : coreNumericSpansCheck 2738 7 480 1155 adaptiveNumericSpans2874_0 adaptiveRows2874 = true := by decide +kernel
theorem adaptiveSpanEvenCache2874_0 : adaptiveSpanEven2874_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain2874_0 : adaptiveSpanEven2874_0.domainCheck 1437 = true := by decide +kernel
theorem adaptiveSpanEvenEntries2874_0 : adaptiveSpanEven2874_0.spans = coreEvenSpans 1437 0 adaptiveNumericSpans2874_0 := by decide +kernel
theorem adaptiveSpanWholeCache2874_0 : adaptiveSpanWhole2874_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain2874_0 : adaptiveSpanWhole2874_0.domainCheck 1437 = true := by decide +kernel
theorem adaptiveSpanWholeEntries2874_0 : adaptiveSpanWhole2874_0.spans = coreWholeSpans 0 adaptiveNumericSpans2874_0 := by decide +kernel
def adaptiveNumericSpans2874_1Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 12 43876455803161755508118928498974568945407311994391654257191295965465003363504049445854676289431444018965557660011321856650233748158673594699955057779917198128392426480427455830293305541362159263717520480880552259423712282546634839544603353076242726091169929976898661082053889549557936428148951735775660677406031979876747893125672657109200587081953071612297344
def adaptiveNumericSpans2874_1 : List AdaptiveNumericSpan := [adaptiveNumericSpans2874_1Chunk0].flatten
def adaptiveSpanEven2874_1 := adaptiveSpanTreeOfSpans (coreEvenSpans 1437 0 adaptiveNumericSpans2874_1)
def adaptiveSpanWhole2874_1 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans2874_1)
theorem adaptiveSpanNumericCheck2874_1 : coreNumericSpansCheck 2738 7 240 385 adaptiveNumericSpans2874_1 adaptiveRows2874 = true := by decide +kernel
theorem adaptiveSpanEvenCache2874_1 : adaptiveSpanEven2874_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain2874_1 : adaptiveSpanEven2874_1.domainCheck 1437 = true := by decide +kernel
theorem adaptiveSpanEvenEntries2874_1 : adaptiveSpanEven2874_1.spans = coreEvenSpans 1437 0 adaptiveNumericSpans2874_1 := by decide +kernel
theorem adaptiveSpanWholeCache2874_1 : adaptiveSpanWhole2874_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain2874_1 : adaptiveSpanWhole2874_1.domainCheck 1437 = true := by decide +kernel
theorem adaptiveSpanWholeEntries2874_1 : adaptiveSpanWhole2874_1.spans = coreWholeSpans 0 adaptiveNumericSpans2874_1 := by decide +kernel
end Erdos883Verified
