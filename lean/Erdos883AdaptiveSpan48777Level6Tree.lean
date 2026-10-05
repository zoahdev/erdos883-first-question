import Erdos883AdaptiveSpan48777Level6TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength48777_6 : adaptiveNumericSpans48777_6.length = 525 := by decide +kernel
theorem adaptiveSpanEvenCache48777_6 : adaptiveSpanEven48777_6.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain48777_6 : adaptiveSpanEven48777_6.domainCheck 24389 = true := by decide +kernel
theorem adaptiveSpanEvenEntries48777_6 : adaptiveSpanEven48777_6.spans = coreEvenSpans 24389 0 adaptiveNumericSpans48777_6 := by
  decide +kernel
theorem adaptiveSpanWholeCache48777_6 : adaptiveSpanWhole48777_6.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain48777_6 : adaptiveSpanWhole48777_6.domainCheck 24389 = true := by decide +kernel
theorem adaptiveSpanWholeEntries48777_6 : adaptiveSpanWhole48777_6.spans = coreWholeSpans 0 adaptiveNumericSpans48777_6 := by
  decide +kernel
end Erdos883Verified
