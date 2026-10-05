import Erdos883AdaptiveSpan104564Level7TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength104564_7 : adaptiveNumericSpans104564_7.length = 642 := by decide +kernel
theorem adaptiveSpanEvenCache104564_7 : adaptiveSpanEven104564_7.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain104564_7 : adaptiveSpanEven104564_7.domainCheck 52282 = true := by decide +kernel
theorem adaptiveSpanEvenEntries104564_7 : adaptiveSpanEven104564_7.spans = coreEvenSpans 52282 0 adaptiveNumericSpans104564_7 := by
  decide +kernel
theorem adaptiveSpanWholeCache104564_7 : adaptiveSpanWhole104564_7.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain104564_7 : adaptiveSpanWhole104564_7.domainCheck 52282 = true := by decide +kernel
theorem adaptiveSpanWholeEntries104564_7 : adaptiveSpanWhole104564_7.spans = coreWholeSpans 0 adaptiveNumericSpans104564_7 := by
  decide +kernel
end Erdos883Verified
