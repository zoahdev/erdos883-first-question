import Erdos883AdaptiveSpan95058Level5TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength95058_5 : adaptiveNumericSpans95058_5.length = 626 := by decide +kernel
theorem adaptiveSpanEvenCache95058_5 : adaptiveSpanEven95058_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain95058_5 : adaptiveSpanEven95058_5.domainCheck 47529 = true := by decide +kernel
theorem adaptiveSpanEvenEntries95058_5 : adaptiveSpanEven95058_5.spans = coreEvenSpans 47529 0 adaptiveNumericSpans95058_5 := by
  decide +kernel
theorem adaptiveSpanWholeCache95058_5 : adaptiveSpanWhole95058_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain95058_5 : adaptiveSpanWhole95058_5.domainCheck 47529 = true := by decide +kernel
theorem adaptiveSpanWholeEntries95058_5 : adaptiveSpanWhole95058_5.spans = coreWholeSpans 0 adaptiveNumericSpans95058_5 := by
  decide +kernel
end Erdos883Verified
