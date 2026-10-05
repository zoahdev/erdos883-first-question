import Erdos883AdaptiveSpan139177Level7TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength139177_7 : adaptiveNumericSpans139177_7.length = 699 := by decide +kernel
theorem adaptiveSpanEvenCache139177_7 : adaptiveSpanEven139177_7.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain139177_7 : adaptiveSpanEven139177_7.domainCheck 69589 = true := by decide +kernel
theorem adaptiveSpanEvenEntries139177_7 : adaptiveSpanEven139177_7.spans = coreEvenSpans 69589 0 adaptiveNumericSpans139177_7 := by
  decide +kernel
theorem adaptiveSpanWholeCache139177_7 : adaptiveSpanWhole139177_7.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain139177_7 : adaptiveSpanWhole139177_7.domainCheck 69589 = true := by decide +kernel
theorem adaptiveSpanWholeEntries139177_7 : adaptiveSpanWhole139177_7.spans = coreWholeSpans 0 adaptiveNumericSpans139177_7 := by
  decide +kernel
end Erdos883Verified
