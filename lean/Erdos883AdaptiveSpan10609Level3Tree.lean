import Erdos883AdaptiveSpan10609Level3TreeData
import Erdos883AdaptiveSpanCompact
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength10609_3 : adaptiveNumericSpans10609_3.length = 364 := by decide +kernel
theorem adaptiveSpanEvenCache10609_3 : adaptiveSpanEven10609_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain10609_3 : adaptiveSpanEven10609_3.domainCheck 5305 = true := by decide +kernel
theorem adaptiveSpanEvenEntries10609_3 : adaptiveSpanEven10609_3.spans = coreEvenSpans 5305 0 adaptiveNumericSpans10609_3 := by
  apply adaptiveSpanTreeOfSpansLinearFuel_spans
  rw [coreEvenSpans_length, adaptiveNumericSpansLength10609_3]
  decide
theorem adaptiveSpanWholeCache10609_3 : adaptiveSpanWhole10609_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain10609_3 : adaptiveSpanWhole10609_3.domainCheck 5305 = true := by decide +kernel
theorem adaptiveSpanWholeEntries10609_3 : adaptiveSpanWhole10609_3.spans = coreWholeSpans 0 adaptiveNumericSpans10609_3 := by
  apply adaptiveSpanTreeOfSpansLinearFuel_spans
  rw [coreWholeSpans_length, adaptiveNumericSpansLength10609_3]
  decide
end Erdos883Verified
