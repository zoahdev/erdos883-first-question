import Erdos883AdaptiveSpan139177Level6TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength139177_6 : adaptiveNumericSpans139177_6.length = 699 := by decide +kernel
theorem adaptiveSpanEvenCache139177_6 : adaptiveSpanEven139177_6.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain139177_6 : adaptiveSpanEven139177_6.domainCheck 69589 = true := by decide +kernel
theorem adaptiveSpanEvenEntries139177_6 : adaptiveSpanEven139177_6.spans = coreEvenSpans 69589 0 adaptiveNumericSpans139177_6 := by
  decide +kernel
theorem adaptiveSpanWholeCache139177_6 : adaptiveSpanWhole139177_6.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain139177_6 : adaptiveSpanWhole139177_6.domainCheck 69589 = true := by decide +kernel
theorem adaptiveSpanWholeEntries139177_6 : adaptiveSpanWhole139177_6.spans = coreWholeSpans 0 adaptiveNumericSpans139177_6 := by
  decide +kernel
end Erdos883Verified
