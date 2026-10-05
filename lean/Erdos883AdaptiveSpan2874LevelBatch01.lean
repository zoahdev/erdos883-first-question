import Erdos883AdaptiveCertificate2874Data
import Erdos883AdaptiveSpanCompactCore
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
def adaptiveNumericSpans2874_2Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 12 43876455803161755508118928498974568945407311994391654257191295965465003363504049445854676289431444018965557660011321856650233748158673594699955057779917198128392426480427455830293305541362159263717520480880552259523608283790849226385707643470352921654157553921235589868717222148923701796935252374544218263766694978123982533253280503644026456727040005672796288
def adaptiveNumericSpans2874_2 : List AdaptiveNumericSpan := [adaptiveNumericSpans2874_2Chunk0].flatten
def adaptiveSpanEven2874_2 := adaptiveSpanTreeOfSpans (coreEvenSpans 1437 0 adaptiveNumericSpans2874_2)
def adaptiveSpanWhole2874_2 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans2874_2)
theorem adaptiveSpanNumericCheck2874_2 : coreNumericSpansCheck 2738 7 720 1001 adaptiveNumericSpans2874_2 adaptiveRows2874 = true := by decide +kernel
theorem adaptiveSpanEvenCache2874_2 : adaptiveSpanEven2874_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain2874_2 : adaptiveSpanEven2874_2.domainCheck 1437 = true := by decide +kernel
theorem adaptiveSpanEvenEntries2874_2 : adaptiveSpanEven2874_2.spans = coreEvenSpans 1437 0 adaptiveNumericSpans2874_2 := by decide +kernel
theorem adaptiveSpanWholeCache2874_2 : adaptiveSpanWhole2874_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain2874_2 : adaptiveSpanWhole2874_2.domainCheck 1437 = true := by decide +kernel
theorem adaptiveSpanWholeEntries2874_2 : adaptiveSpanWhole2874_2.spans = coreWholeSpans 0 adaptiveNumericSpans2874_2 := by decide +kernel
def adaptiveNumericSpans2874_3Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 12 43876455803161755508118928498974568945407311994391654257191295965465003363504049445854676289431444018965557660011321856650233748158673594699955057779917198128392426480427455830293305541362159263717520480880552259948166289078760370460400877644602781491359001560866902248621671655425727453519906811020753978375110156284186633518198194452076562742252996686512256
def adaptiveNumericSpans2874_3 : List AdaptiveNumericSpan := [adaptiveNumericSpans2874_3Chunk0].flatten
def adaptiveSpanEven2874_3 := adaptiveSpanTreeOfSpans (coreEvenSpans 1437 0 adaptiveNumericSpans2874_3)
def adaptiveSpanWhole2874_3 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans2874_3)
theorem adaptiveSpanNumericCheck2874_3 : coreNumericSpansCheck 2738 7 1920 2431 adaptiveNumericSpans2874_3 adaptiveRows2874 = true := by decide +kernel
theorem adaptiveSpanEvenCache2874_3 : adaptiveSpanEven2874_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain2874_3 : adaptiveSpanEven2874_3.domainCheck 1437 = true := by decide +kernel
theorem adaptiveSpanEvenEntries2874_3 : adaptiveSpanEven2874_3.spans = coreEvenSpans 1437 0 adaptiveNumericSpans2874_3 := by decide +kernel
theorem adaptiveSpanWholeCache2874_3 : adaptiveSpanWhole2874_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain2874_3 : adaptiveSpanWhole2874_3.domainCheck 1437 = true := by decide +kernel
theorem adaptiveSpanWholeEntries2874_3 : adaptiveSpanWhole2874_3.spans = coreWholeSpans 0 adaptiveNumericSpans2874_3 := by decide +kernel
end Erdos883Verified
