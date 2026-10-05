import Erdos883AdaptiveSpan11671Level3TreeData
import Erdos883AdaptiveSpanCompact
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength11671_3 : adaptiveNumericSpans11671_3.length = 375 := by decide +kernel
theorem adaptiveSpanEvenCache11671_3 : adaptiveSpanEven11671_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain11671_3 : adaptiveSpanEven11671_3.domainCheck 5836 = true := by decide +kernel
theorem adaptiveSpanEvenEntries11671_3 : adaptiveSpanEven11671_3.spans = coreEvenSpans 5836 0 adaptiveNumericSpans11671_3 := by
  apply adaptiveSpanTreeOfSpansLinearFuel_spans
  rw [coreEvenSpans_length, adaptiveNumericSpansLength11671_3]
  decide
theorem adaptiveSpanWholeCache11671_3 : adaptiveSpanWhole11671_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain11671_3 : adaptiveSpanWhole11671_3.domainCheck 5836 = true := by decide +kernel
theorem adaptiveSpanWholeEntries11671_3 : adaptiveSpanWhole11671_3.spans = coreWholeSpans 0 adaptiveNumericSpans11671_3 := by
  apply adaptiveSpanTreeOfSpansLinearFuel_spans
  rw [coreWholeSpans_length, adaptiveNumericSpansLength11671_3]
  decide
end Erdos883Verified
