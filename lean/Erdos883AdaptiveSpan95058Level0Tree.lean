import Erdos883AdaptiveSpan95058Level0TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength95058_0 : adaptiveNumericSpans95058_0.length = 626 := by decide +kernel
theorem adaptiveSpanEvenCache95058_0 : adaptiveSpanEven95058_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain95058_0 : adaptiveSpanEven95058_0.domainCheck 47529 = true := by decide +kernel
theorem adaptiveSpanEvenEntries95058_0 : adaptiveSpanEven95058_0.spans = coreEvenSpans 47529 0 adaptiveNumericSpans95058_0 := by
  decide +kernel
theorem adaptiveSpanWholeCache95058_0 : adaptiveSpanWhole95058_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain95058_0 : adaptiveSpanWhole95058_0.domainCheck 47529 = true := by decide +kernel
theorem adaptiveSpanWholeEntries95058_0 : adaptiveSpanWhole95058_0.spans = coreWholeSpans 0 adaptiveNumericSpans95058_0 := by
  decide +kernel
end Erdos883Verified
