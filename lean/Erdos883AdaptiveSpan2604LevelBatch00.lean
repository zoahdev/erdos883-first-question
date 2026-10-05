import Erdos883AdaptiveCertificate2604Data
import Erdos883AdaptiveSpanCompactCore
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
def adaptiveNumericSpans2604_0Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 13 51519288284758486841748895641274135863270320878358321217857294594893872439455487146660861077678356794262141237928149009668323400220267397284622886812342399604620169987537394686246549030219284707829439844853706351686180538552551072127123303899225528140989002783241943376782613156035385977454880520802454644228654402722628345787363427921738545147491712420010847599476789646175745700758814848
def adaptiveNumericSpans2604_0 : List AdaptiveNumericSpan := [adaptiveNumericSpans2604_0Chunk0].flatten
def adaptiveSpanEven2604_0 := adaptiveSpanTreeOfSpans (coreEvenSpans 1302 0 adaptiveNumericSpans2604_0)
def adaptiveSpanWhole2604_0 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans2604_0)
theorem adaptiveSpanNumericCheck2604_0 : coreNumericSpansCheck 2541 7 480 1155 adaptiveNumericSpans2604_0 adaptiveRows2604 = true := by decide +kernel
theorem adaptiveSpanEvenCache2604_0 : adaptiveSpanEven2604_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain2604_0 : adaptiveSpanEven2604_0.domainCheck 1302 = true := by decide +kernel
theorem adaptiveSpanEvenEntries2604_0 : adaptiveSpanEven2604_0.spans = coreEvenSpans 1302 0 adaptiveNumericSpans2604_0 := by decide +kernel
theorem adaptiveSpanWholeCache2604_0 : adaptiveSpanWhole2604_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain2604_0 : adaptiveSpanWhole2604_0.domainCheck 1302 = true := by decide +kernel
theorem adaptiveSpanWholeEntries2604_0 : adaptiveSpanWhole2604_0.spans = coreWholeSpans 0 adaptiveNumericSpans2604_0 := by decide +kernel
def adaptiveNumericSpans2604_1Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 11 32060531810058459773599096193333751346946346430533747356842106783813081930213886489316752597315479379743481109278377479000455034010785617852141879524907986257932146647842607468025706980781808222000386576195857625768457574096593671509217489748675013828771418830568579063295608526200062552160270237090880790568896307134311629324416
def adaptiveNumericSpans2604_1 : List AdaptiveNumericSpan := [adaptiveNumericSpans2604_1Chunk0].flatten
def adaptiveSpanEven2604_1 := adaptiveSpanTreeOfSpans (coreEvenSpans 1302 0 adaptiveNumericSpans2604_1)
def adaptiveSpanWhole2604_1 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans2604_1)
theorem adaptiveSpanNumericCheck2604_1 : coreNumericSpansCheck 2541 7 240 385 adaptiveNumericSpans2604_1 adaptiveRows2604 = true := by decide +kernel
theorem adaptiveSpanEvenCache2604_1 : adaptiveSpanEven2604_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain2604_1 : adaptiveSpanEven2604_1.domainCheck 1302 = true := by decide +kernel
theorem adaptiveSpanEvenEntries2604_1 : adaptiveSpanEven2604_1.spans = coreEvenSpans 1302 0 adaptiveNumericSpans2604_1 := by decide +kernel
theorem adaptiveSpanWholeCache2604_1 : adaptiveSpanWhole2604_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain2604_1 : adaptiveSpanWhole2604_1.domainCheck 1302 = true := by decide +kernel
theorem adaptiveSpanWholeEntries2604_1 : adaptiveSpanWhole2604_1.spans = coreWholeSpans 0 adaptiveNumericSpans2604_1 := by decide +kernel
end Erdos883Verified
