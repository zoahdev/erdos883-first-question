import Erdos883AdaptiveSpan104564Level5TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength104564_5 : adaptiveNumericSpans104564_5.length = 642 := by decide +kernel
theorem adaptiveSpanEvenCache104564_5 : adaptiveSpanEven104564_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain104564_5 : adaptiveSpanEven104564_5.domainCheck 52282 = true := by decide +kernel
theorem adaptiveSpanEvenEntries104564_5 : adaptiveSpanEven104564_5.spans = coreEvenSpans 52282 0 adaptiveNumericSpans104564_5 := by
  decide +kernel
theorem adaptiveSpanWholeCache104564_5 : adaptiveSpanWhole104564_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain104564_5 : adaptiveSpanWhole104564_5.domainCheck 52282 = true := by decide +kernel
theorem adaptiveSpanWholeEntries104564_5 : adaptiveSpanWhole104564_5.spans = coreWholeSpans 0 adaptiveNumericSpans104564_5 := by
  decide +kernel
end Erdos883Verified
