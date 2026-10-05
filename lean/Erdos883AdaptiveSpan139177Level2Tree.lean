import Erdos883AdaptiveSpan139177Level2TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength139177_2 : adaptiveNumericSpans139177_2.length = 699 := by decide +kernel
theorem adaptiveSpanEvenCache139177_2 : adaptiveSpanEven139177_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain139177_2 : adaptiveSpanEven139177_2.domainCheck 69589 = true := by decide +kernel
theorem adaptiveSpanEvenEntries139177_2 : adaptiveSpanEven139177_2.spans = coreEvenSpans 69589 0 adaptiveNumericSpans139177_2 := by
  decide +kernel
theorem adaptiveSpanWholeCache139177_2 : adaptiveSpanWhole139177_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain139177_2 : adaptiveSpanWhole139177_2.domainCheck 69589 = true := by decide +kernel
theorem adaptiveSpanWholeEntries139177_2 : adaptiveSpanWhole139177_2.spans = coreWholeSpans 0 adaptiveNumericSpans139177_2 := by
  decide +kernel
end Erdos883Verified
