import Erdos883AdaptiveSpan139177Level0TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength139177_0 : adaptiveNumericSpans139177_0.length = 699 := by decide +kernel
theorem adaptiveSpanEvenCache139177_0 : adaptiveSpanEven139177_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain139177_0 : adaptiveSpanEven139177_0.domainCheck 69589 = true := by decide +kernel
theorem adaptiveSpanEvenEntries139177_0 : adaptiveSpanEven139177_0.spans = coreEvenSpans 69589 0 adaptiveNumericSpans139177_0 := by
  decide +kernel
theorem adaptiveSpanWholeCache139177_0 : adaptiveSpanWhole139177_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain139177_0 : adaptiveSpanWhole139177_0.domainCheck 69589 = true := by decide +kernel
theorem adaptiveSpanWholeEntries139177_0 : adaptiveSpanWhole139177_0.spans = coreWholeSpans 0 adaptiveNumericSpans139177_0 := by
  decide +kernel
end Erdos883Verified
