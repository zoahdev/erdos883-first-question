import Erdos883AdaptiveSpan14124Level8TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength14124_8 : adaptiveNumericSpans14124_8.length = 391 := by decide +kernel
theorem adaptiveSpanEvenCache14124_8 : adaptiveSpanEven14124_8.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain14124_8 : adaptiveSpanEven14124_8.domainCheck 7062 = true := by decide +kernel
theorem adaptiveSpanEvenEntries14124_8 : adaptiveSpanEven14124_8.spans = coreEvenSpans 7062 0 adaptiveNumericSpans14124_8 := by
  decide +kernel
theorem adaptiveSpanWholeCache14124_8 : adaptiveSpanWhole14124_8.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain14124_8 : adaptiveSpanWhole14124_8.domainCheck 7062 = true := by decide +kernel
theorem adaptiveSpanWholeEntries14124_8 : adaptiveSpanWhole14124_8.spans = coreWholeSpans 0 adaptiveNumericSpans14124_8 := by
  decide +kernel
end Erdos883Verified
