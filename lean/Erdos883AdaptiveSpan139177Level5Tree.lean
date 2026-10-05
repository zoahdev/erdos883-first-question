import Erdos883AdaptiveSpan139177Level5TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength139177_5 : adaptiveNumericSpans139177_5.length = 699 := by decide +kernel
theorem adaptiveSpanEvenCache139177_5 : adaptiveSpanEven139177_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain139177_5 : adaptiveSpanEven139177_5.domainCheck 69589 = true := by decide +kernel
theorem adaptiveSpanEvenEntries139177_5 : adaptiveSpanEven139177_5.spans = coreEvenSpans 69589 0 adaptiveNumericSpans139177_5 := by
  decide +kernel
theorem adaptiveSpanWholeCache139177_5 : adaptiveSpanWhole139177_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain139177_5 : adaptiveSpanWhole139177_5.domainCheck 69589 = true := by decide +kernel
theorem adaptiveSpanWholeEntries139177_5 : adaptiveSpanWhole139177_5.spans = coreWholeSpans 0 adaptiveNumericSpans139177_5 := by
  decide +kernel
end Erdos883Verified
