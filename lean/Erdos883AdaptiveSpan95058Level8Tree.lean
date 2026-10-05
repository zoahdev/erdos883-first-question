import Erdos883AdaptiveSpan95058Level8TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength95058_8 : adaptiveNumericSpans95058_8.length = 626 := by decide +kernel
theorem adaptiveSpanEvenCache95058_8 : adaptiveSpanEven95058_8.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain95058_8 : adaptiveSpanEven95058_8.domainCheck 47529 = true := by decide +kernel
theorem adaptiveSpanEvenEntries95058_8 : adaptiveSpanEven95058_8.spans = coreEvenSpans 47529 0 adaptiveNumericSpans95058_8 := by
  decide +kernel
theorem adaptiveSpanWholeCache95058_8 : adaptiveSpanWhole95058_8.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain95058_8 : adaptiveSpanWhole95058_8.domainCheck 47529 = true := by decide +kernel
theorem adaptiveSpanWholeEntries95058_8 : adaptiveSpanWhole95058_8.spans = coreWholeSpans 0 adaptiveNumericSpans95058_8 := by
  decide +kernel
end Erdos883Verified
