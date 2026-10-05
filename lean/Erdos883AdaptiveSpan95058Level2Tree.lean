import Erdos883AdaptiveSpan95058Level2TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength95058_2 : adaptiveNumericSpans95058_2.length = 626 := by decide +kernel
theorem adaptiveSpanEvenCache95058_2 : adaptiveSpanEven95058_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain95058_2 : adaptiveSpanEven95058_2.domainCheck 47529 = true := by decide +kernel
theorem adaptiveSpanEvenEntries95058_2 : adaptiveSpanEven95058_2.spans = coreEvenSpans 47529 0 adaptiveNumericSpans95058_2 := by
  decide +kernel
theorem adaptiveSpanWholeCache95058_2 : adaptiveSpanWhole95058_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain95058_2 : adaptiveSpanWhole95058_2.domainCheck 47529 = true := by decide +kernel
theorem adaptiveSpanWholeEntries95058_2 : adaptiveSpanWhole95058_2.spans = coreWholeSpans 0 adaptiveNumericSpans95058_2 := by
  decide +kernel
end Erdos883Verified
