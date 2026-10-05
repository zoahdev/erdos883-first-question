import Erdos883AdaptiveSpan95058Level6TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength95058_6 : adaptiveNumericSpans95058_6.length = 626 := by decide +kernel
theorem adaptiveSpanEvenCache95058_6 : adaptiveSpanEven95058_6.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain95058_6 : adaptiveSpanEven95058_6.domainCheck 47529 = true := by decide +kernel
theorem adaptiveSpanEvenEntries95058_6 : adaptiveSpanEven95058_6.spans = coreEvenSpans 47529 0 adaptiveNumericSpans95058_6 := by
  decide +kernel
theorem adaptiveSpanWholeCache95058_6 : adaptiveSpanWhole95058_6.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain95058_6 : adaptiveSpanWhole95058_6.domainCheck 47529 = true := by decide +kernel
theorem adaptiveSpanWholeEntries95058_6 : adaptiveSpanWhole95058_6.spans = coreWholeSpans 0 adaptiveNumericSpans95058_6 := by
  decide +kernel
end Erdos883Verified
