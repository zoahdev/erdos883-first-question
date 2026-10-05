import Erdos883AdaptiveSpan95058Level3TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength95058_3 : adaptiveNumericSpans95058_3.length = 626 := by decide +kernel
theorem adaptiveSpanEvenCache95058_3 : adaptiveSpanEven95058_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain95058_3 : adaptiveSpanEven95058_3.domainCheck 47529 = true := by decide +kernel
theorem adaptiveSpanEvenEntries95058_3 : adaptiveSpanEven95058_3.spans = coreEvenSpans 47529 0 adaptiveNumericSpans95058_3 := by
  decide +kernel
theorem adaptiveSpanWholeCache95058_3 : adaptiveSpanWhole95058_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain95058_3 : adaptiveSpanWhole95058_3.domainCheck 47529 = true := by decide +kernel
theorem adaptiveSpanWholeEntries95058_3 : adaptiveSpanWhole95058_3.spans = coreWholeSpans 0 adaptiveNumericSpans95058_3 := by
  decide +kernel
end Erdos883Verified
