import Erdos883AdaptiveSpan48777Level7TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength48777_7 : adaptiveNumericSpans48777_7.length = 525 := by decide +kernel
theorem adaptiveSpanEvenCache48777_7 : adaptiveSpanEven48777_7.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain48777_7 : adaptiveSpanEven48777_7.domainCheck 24389 = true := by decide +kernel
theorem adaptiveSpanEvenEntries48777_7 : adaptiveSpanEven48777_7.spans = coreEvenSpans 24389 0 adaptiveNumericSpans48777_7 := by
  decide +kernel
theorem adaptiveSpanWholeCache48777_7 : adaptiveSpanWhole48777_7.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain48777_7 : adaptiveSpanWhole48777_7.domainCheck 24389 = true := by decide +kernel
theorem adaptiveSpanWholeEntries48777_7 : adaptiveSpanWhole48777_7.spans = coreWholeSpans 0 adaptiveNumericSpans48777_7 := by
  decide +kernel
end Erdos883Verified
