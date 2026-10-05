import Erdos883AdaptiveSpan185246Level3TreeData
import Erdos883AdaptiveSpanCompact
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength185246_3 : adaptiveNumericSpans185246_3.length = 769 := by decide +kernel
theorem adaptiveSpanEvenCache185246_3 : adaptiveSpanEven185246_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain185246_3 : adaptiveSpanEven185246_3.domainCheck 92623 = true := by decide +kernel
theorem adaptiveSpanEvenEntries185246_3 : adaptiveSpanEven185246_3.spans = coreEvenSpans 92623 0 adaptiveNumericSpans185246_3 := by
  apply adaptiveSpanTreeOfSpansLinearFuel_spans
  rw [coreEvenSpans_length, adaptiveNumericSpansLength185246_3]
  decide
theorem adaptiveSpanWholeCache185246_3 : adaptiveSpanWhole185246_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain185246_3 : adaptiveSpanWhole185246_3.domainCheck 92623 = true := by decide +kernel
theorem adaptiveSpanWholeEntries185246_3 : adaptiveSpanWhole185246_3.spans = coreWholeSpans 0 adaptiveNumericSpans185246_3 := by
  apply adaptiveSpanTreeOfSpansLinearFuel_spans
  rw [coreWholeSpans_length, adaptiveNumericSpansLength185246_3]
  decide
end Erdos883Verified
