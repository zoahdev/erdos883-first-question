import Erdos883AdaptiveSpan139177Level3TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength139177_3 : adaptiveNumericSpans139177_3.length = 699 := by decide +kernel
theorem adaptiveSpanEvenCache139177_3 : adaptiveSpanEven139177_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain139177_3 : adaptiveSpanEven139177_3.domainCheck 69589 = true := by decide +kernel
theorem adaptiveSpanEvenEntries139177_3 : adaptiveSpanEven139177_3.spans = coreEvenSpans 69589 0 adaptiveNumericSpans139177_3 := by
  decide +kernel
theorem adaptiveSpanWholeCache139177_3 : adaptiveSpanWhole139177_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain139177_3 : adaptiveSpanWhole139177_3.domainCheck 69589 = true := by decide +kernel
theorem adaptiveSpanWholeEntries139177_3 : adaptiveSpanWhole139177_3.spans = coreWholeSpans 0 adaptiveNumericSpans139177_3 := by
  decide +kernel
end Erdos883Verified
