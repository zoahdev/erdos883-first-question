import Erdos883AdaptiveSpan139177Level1TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength139177_1 : adaptiveNumericSpans139177_1.length = 699 := by decide +kernel
theorem adaptiveSpanEvenCache139177_1 : adaptiveSpanEven139177_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain139177_1 : adaptiveSpanEven139177_1.domainCheck 69589 = true := by decide +kernel
theorem adaptiveSpanEvenEntries139177_1 : adaptiveSpanEven139177_1.spans = coreEvenSpans 69589 0 adaptiveNumericSpans139177_1 := by
  decide +kernel
theorem adaptiveSpanWholeCache139177_1 : adaptiveSpanWhole139177_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain139177_1 : adaptiveSpanWhole139177_1.domainCheck 69589 = true := by decide +kernel
theorem adaptiveSpanWholeEntries139177_1 : adaptiveSpanWhole139177_1.spans = coreWholeSpans 0 adaptiveNumericSpans139177_1 := by
  decide +kernel
end Erdos883Verified
