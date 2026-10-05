import Erdos883AdaptiveSpan10609Level0TreeData
import Erdos883AdaptiveSpanCompact
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength10609_0 : adaptiveNumericSpans10609_0.length = 364 := by decide +kernel
theorem adaptiveSpanEvenCache10609_0 : adaptiveSpanEven10609_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain10609_0 : adaptiveSpanEven10609_0.domainCheck 5305 = true := by decide +kernel
theorem adaptiveSpanEvenEntries10609_0 : adaptiveSpanEven10609_0.spans = coreEvenSpans 5305 0 adaptiveNumericSpans10609_0 := by
  apply adaptiveSpanTreeOfSpansLinearFuel_spans
  rw [coreEvenSpans_length, adaptiveNumericSpansLength10609_0]
  decide
theorem adaptiveSpanWholeCache10609_0 : adaptiveSpanWhole10609_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain10609_0 : adaptiveSpanWhole10609_0.domainCheck 5305 = true := by decide +kernel
theorem adaptiveSpanWholeEntries10609_0 : adaptiveSpanWhole10609_0.spans = coreWholeSpans 0 adaptiveNumericSpans10609_0 := by
  apply adaptiveSpanTreeOfSpansLinearFuel_spans
  rw [coreWholeSpans_length, adaptiveNumericSpansLength10609_0]
  decide
end Erdos883Verified
