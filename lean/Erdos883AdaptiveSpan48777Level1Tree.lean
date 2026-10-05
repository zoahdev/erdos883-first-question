import Erdos883AdaptiveSpan48777Level1TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength48777_1 : adaptiveNumericSpans48777_1.length = 525 := by decide +kernel
theorem adaptiveSpanEvenCache48777_1 : adaptiveSpanEven48777_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain48777_1 : adaptiveSpanEven48777_1.domainCheck 24389 = true := by decide +kernel
theorem adaptiveSpanEvenEntries48777_1 : adaptiveSpanEven48777_1.spans = coreEvenSpans 24389 0 adaptiveNumericSpans48777_1 := by
  decide +kernel
theorem adaptiveSpanWholeCache48777_1 : adaptiveSpanWhole48777_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain48777_1 : adaptiveSpanWhole48777_1.domainCheck 24389 = true := by decide +kernel
theorem adaptiveSpanWholeEntries48777_1 : adaptiveSpanWhole48777_1.spans = coreWholeSpans 0 adaptiveNumericSpans48777_1 := by
  decide +kernel
end Erdos883Verified
