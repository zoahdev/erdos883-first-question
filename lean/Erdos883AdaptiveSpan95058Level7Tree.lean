import Erdos883AdaptiveSpan95058Level7TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength95058_7 : adaptiveNumericSpans95058_7.length = 626 := by decide +kernel
theorem adaptiveSpanEvenCache95058_7 : adaptiveSpanEven95058_7.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain95058_7 : adaptiveSpanEven95058_7.domainCheck 47529 = true := by decide +kernel
theorem adaptiveSpanEvenEntries95058_7 : adaptiveSpanEven95058_7.spans = coreEvenSpans 47529 0 adaptiveNumericSpans95058_7 := by
  decide +kernel
theorem adaptiveSpanWholeCache95058_7 : adaptiveSpanWhole95058_7.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain95058_7 : adaptiveSpanWhole95058_7.domainCheck 47529 = true := by decide +kernel
theorem adaptiveSpanWholeEntries95058_7 : adaptiveSpanWhole95058_7.spans = coreWholeSpans 0 adaptiveNumericSpans95058_7 := by
  decide +kernel
end Erdos883Verified
