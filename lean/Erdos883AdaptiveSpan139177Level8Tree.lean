import Erdos883AdaptiveSpan139177Level8TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength139177_8 : adaptiveNumericSpans139177_8.length = 699 := by decide +kernel
theorem adaptiveSpanEvenCache139177_8 : adaptiveSpanEven139177_8.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain139177_8 : adaptiveSpanEven139177_8.domainCheck 69589 = true := by decide +kernel
theorem adaptiveSpanEvenEntries139177_8 : adaptiveSpanEven139177_8.spans = coreEvenSpans 69589 0 adaptiveNumericSpans139177_8 := by
  decide +kernel
theorem adaptiveSpanWholeCache139177_8 : adaptiveSpanWhole139177_8.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain139177_8 : adaptiveSpanWhole139177_8.domainCheck 69589 = true := by decide +kernel
theorem adaptiveSpanWholeEntries139177_8 : adaptiveSpanWhole139177_8.spans = coreWholeSpans 0 adaptiveNumericSpans139177_8 := by
  decide +kernel
end Erdos883Verified
